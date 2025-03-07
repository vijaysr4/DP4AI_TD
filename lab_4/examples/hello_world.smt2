;; Define the logic
;;
;; Optional, but recommended: the solver should be able to identify the logic
;; But not the solvers may not support a logic - so this check allows the 
;; solver to fail immediately.
;;
(set-logic QF_UF)

;; Declare variables first

;; Formally, a variable is a 0-arity function
;; It is called a constant in SMT-LIB (that is the formal name in first-order logic)
(declare-fun a () Bool)
;; Equivalently we can use the declare-const command
(declare-const b Bool)

;; assert formulas (each assert is seens as a conjunct)

(assert
  ;; we want to check validty
  ;; \phi is valid iff not \phi is satisfiable
  (not
     (=
       (and a b)
       (not (or (not a) (not b) ))
     )
  )
)

(check-sat)