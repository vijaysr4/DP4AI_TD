;; The concrete system is unsafe, the abstract system must be unsafe.
;; The abstract system with predicates x <= 10, x >= 5 should be unsafe too.
;; It's not if the initial state encoding of the properties for IA is wrong.
(set-info :source |printed by MathSAT|)
(declare-fun x__AT0 () Real)
(declare-fun x__AT1 () Real)
(define-fun .def_1 () Real (! x__AT0 :next x__AT1))
(define-fun .def_2 () Bool (! (< x__AT0 (to_real 10)) :init true))
(define-fun .def_3 () Bool (! (>= x__AT0 (to_real 5)) :invar-property 0))
(define-fun .def_4 () Bool (! (>= x__AT1 (to_real 5)) :trans true))
(assert true)
