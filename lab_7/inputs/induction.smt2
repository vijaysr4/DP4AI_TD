(set-info :source |printed by MathSAT|)
(declare-fun i__AT0 () Int)
(declare-fun i__AT1 () Int)
(define-fun .def_8 () Int (! i__AT0 :next i__AT1))

(define-fun .init_formula () Bool (! (= i__AT0 2) :init true))
(define-fun .trans_formula () Bool (! (and
  (=> (or (< i__AT0 5) (and (> i__AT0 6) (<= i__AT0 10) ) ) (= i__AT1 (+ i__AT0 1)))
  (=> (or (= i__AT0 5) (= i__AT0 6) ) (= i__AT1 i__AT0))
) :trans true))

(define-fun .prop_formula () Bool (! (<= i__AT0 5) :invar-property 0))

(assert true)
