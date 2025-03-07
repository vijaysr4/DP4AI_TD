(set-logic QF_NRA)

(declare-fun b__AT0 () Bool)
(declare-fun b__AT1 () Bool)
(declare-fun b__abs_AT0 () Bool)
(declare-fun b__abs_AT1 () Bool)
(declare-fun counter__AT0 () Real)
(declare-fun counter__AT1 () Real)

(define-fun nvdef_2 () Bool (! b__AT0 :next b__AT1))
(define-fun nvdef_3 () Bool (! b__abs_AT0 :next b__abs_AT1))
(define-fun nvdef_4 () Real (! counter__AT0 :next counter__AT1))


(define-fun .init () Bool (! (and (= counter__AT0 (to_real 0))
(and (= b__AT0 b__abs_AT0) b__AT0)
) :init true))

(define-fun .trans () Bool (! (and (= counter__AT1 (+ counter__AT0 (to_real 1)) )
(and
  (= b__AT0 b__abs_AT0)
  (= b__AT1 (not b__abs_AT0))
  (= b__AT1 b__abs_AT1)
)
) :trans true))


(define-fun .invar-property () Bool (! (< counter__AT0 (to_real 5)) :invar-property 0))
