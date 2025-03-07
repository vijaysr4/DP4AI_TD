;; one_step.smt2
(set-logic QF_LRA)
(set-option :produce-models true)

;; Declare 4 Real variables for the robot positions.
(declare-fun x0 () Real)
(declare-fun y0 () Real)
(declare-fun xf () Real)
(declare-fun yf () Real)

;; Declare Boolean variables for the directions.
(declare-fun left () Bool)
(declare-fun right () Bool)
(declare-fun up () Bool)
(declare-fun down () Bool)

;; Declare a Real variable for the distance traveled.
(declare-fun distance () Real)

;; Assert the initial and target positions.
(assert (= x0 1))
(assert (and (= y0 3) (= xf 1) (= yf 5)))

;; One-hot encoding for the directions: exactly one must be true.
(assert
  (and
    (or left right up down)
    (and
         (=> left  (and (not right) (not up) (not down)))
         (=> right (and (not left)  (not up) (not down)))
         (=> up    (and (not left)  (not right) (not down)))
         (=> down  (and (not left)  (not right) (not up)))
    )
  )
)

;; Movement constraints:
;; For horizontal moves (left/right), y remains constant.
(assert (=> (or left right) (= y0 yf)))
;; For vertical moves (up/down), x remains constant.
(assert (=> (or up down) (= x0 xf)))
;; Direction-specific ordering:
(assert (=> left  (>= x0 xf)))
(assert (=> right (<= x0 xf)))
(assert (=> up    (<= y0 yf)))
(assert (=> down  (>= y0 yf)))

;; Compute the distance moved.
(assert
  (and
    (=> (or left right) (= distance (- xf x0)))
    (=> (or up down)    (= distance (- yf y0)))
  )
)

;; Define the avoid_obstacle function.
;; This function ensures that the move from (xs, ys) to (xd, yd)
;; avoids the rectangular obstacle defined by [x_lower, x_upper] x [y_lower, y_upper].
(define-fun avoid_obstacle ((xs Real) (ys Real)
                            (xd Real) (yd Real)
                            (x_lower Real) (x_upper Real)
                            (y_lower Real) (y_upper Real)) Bool
  (or
    ; The move is entirely to the left of the obstacle.
    (and (<= xs x_lower) (<= xd x_lower))
    ; The move is entirely to the right of the obstacle.
    (and (>= xs x_upper) (>= xd x_upper))
    ; The move is entirely below the obstacle.
    (and (<= ys y_lower) (<= yd y_lower))
    ; The move is entirely above the obstacle.
    (and (>= ys y_upper) (>= yd y_upper))
  )
)

;; Obstacle 1: rectangle with lower-left (3,2) and upper-right (5,4)
(assert (avoid_obstacle x0 y0 xf yf 3 5 2 4))
;; Obstacle 2: rectangle with lower-left (1,2) and upper-right (7,2)
(assert (avoid_obstacle x0 y0 xf yf 1 7 2 2))

(check-sat)
(get-model)
