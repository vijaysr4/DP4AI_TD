;; multiple_step.smt2
(set-logic QF_LRA)
(set-option :produce-models true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Position Variables: For steps 0,1,2,3 (k = 3 actions)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun x0 () Real)
(declare-fun y0 () Real)

(declare-fun x1 () Real)
(declare-fun y1 () Real)

(declare-fun x2 () Real)
(declare-fun y2 () Real)

(declare-fun x3 () Real)
(declare-fun y3 () Real)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Direction Variables: For each of the 3 actions (steps 0,1,2)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Step 0
(declare-fun left_0 () Bool)
(declare-fun right_0 () Bool)
(declare-fun up_0 () Bool)
(declare-fun down_0 () Bool)

;; Step 1
(declare-fun left_1 () Bool)
(declare-fun right_1 () Bool)
(declare-fun up_1 () Bool)
(declare-fun down_1 () Bool)

;; Step 2
(declare-fun left_2 () Bool)
(declare-fun right_2 () Bool)
(declare-fun up_2 () Bool)
(declare-fun down_2 () Bool)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Initial and Target Constraints
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (= x0 1))
(assert (= y0 3))
(assert (= x3 1))
(assert (= y3 5))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; One-Hot Constraints for Each Step
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Step 0 one-hot
(assert
  (and
    (or left_0 right_0 up_0 down_0)
    (and
      (=> left_0  (and (not right_0) (not up_0) (not down_0)))
      (=> right_0 (and (not left_0) (not up_0) (not down_0)))
      (=> up_0    (and (not left_0) (not right_0) (not down_0)))
      (=> down_0  (and (not left_0) (not right_0) (not up_0)))
    )
  )
)

;; Step 1 one-hot
(assert
  (and
    (or left_1 right_1 up_1 down_1)
    (and
      (=> left_1  (and (not right_1) (not up_1) (not down_1)))
      (=> right_1 (and (not left_1) (not up_1) (not down_1)))
      (=> up_1    (and (not left_1) (not right_1) (not down_1)))
      (=> down_1  (and (not left_1) (not right_1) (not up_1)))
    )
  )
)

;; Step 2 one-hot
(assert
  (and
    (or left_2 right_2 up_2 down_2)
    (and
      (=> left_2  (and (not right_2) (not up_2) (not down_2)))
      (=> right_2 (and (not left_2) (not up_2) (not down_2)))
      (=> up_2    (and (not left_2) (not right_2) (not down_2)))
      (=> down_2  (and (not left_2) (not right_2) (not up_2)))
    )
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Movement Constraints for Each Step
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Step 0: from (x0, y0) to (x1, y1)
(assert (=> (or left_0 right_0) (= y0 y1)))
(assert (=> (or up_0 down_0)    (= x0 x1)))
(assert (=> left_0  (>= x0 x1)))
(assert (=> right_0 (<= x0 x1)))
(assert (=> up_0    (<= y0 y1)))
(assert (=> down_0  (>= y0 y1)))

;; Step 1: from (x1, y1) to (x2, y2)
(assert (=> (or left_1 right_1) (= y1 y2)))
(assert (=> (or up_1 down_1)    (= x1 x2)))
(assert (=> left_1  (>= x1 x2)))
(assert (=> right_1 (<= x1 x2)))
(assert (=> up_1    (<= y1 y2)))
(assert (=> down_1  (>= y1 y2)))

;; Step 2: from (x2, y2) to (x3, y3)
(assert (=> (or left_2 right_2) (= y2 y3)))
(assert (=> (or up_2 down_2)    (= x2 x3)))
(assert (=> left_2  (>= x2 x3)))
(assert (=> right_2 (<= x2 x3)))
(assert (=> up_2    (<= y2 y3)))
(assert (=> down_2  (>= y2 y3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Obstacle Avoidance Function
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun avoid_obstacle ((xs Real) (ys Real)
                            (xd Real) (yd Real)
                            (x_lower Real) (x_upper Real)
                            (y_lower Real) (y_upper Real)) Bool
  (or
    ; The segment is entirely to the left of the obstacle.
    (and (<= xs x_lower) (<= xd x_lower))
    ; The segment is entirely to the right of the obstacle.
    (and (>= xs x_upper) (>= xd x_upper))
    ; The segment is entirely below the obstacle.
    (and (<= ys y_lower) (<= yd y_lower))
    ; The segment is entirely above the obstacle.
    (and (>= ys y_upper) (>= yd y_upper))
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Obstacle Avoidance Constraints for Each Step
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example: one obstacle with lower-left (3,2) and upper-right (5,4)
(assert (avoid_obstacle x0 y0 x1 y1 3 5 2 4))
(assert (avoid_obstacle x1 y1 x2 y2 3 5 2 4))
(assert (avoid_obstacle x2 y2 x3 y3 3 5 2 4))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Check Satisfiability and Get Model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(check-sat)
(get-model)
