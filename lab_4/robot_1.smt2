;; robot_1.smt2
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

;; Initial and target positions.
(assert (= x0 1))
(assert (and (= y0 3) (= xf 1) (= yf 5)))

;; One-hot encoding for the directions.
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
;; When moving horizontally (left or right) the y-coordinate does not change.
(assert (=> (or left right) (= y0 yf)))
;; When moving vertically (up or down) the x-coordinate does not change.
(assert (=> (or up down) (= x0 xf)))
;; For left/right moves: the x-coordinate changes in the correct direction.
(assert (=> left  (>= x0 xf)))
(assert (=> right (<= x0 xf)))
;; For up/down moves: the y-coordinate changes in the correct direction.
(assert (=> down (>= y0 yf)))
(assert (=> up   (<= y0 yf)))

;; Compute the distance moved.
(assert
  (and
    (=> (or left right) (= distance (- xf x0)))
    (=> (or up down)    (= distance (- yf y0)))
  )
)

(check-sat)
(get-model)
