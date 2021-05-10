; Example from paper
;(set-logic QBVF)

(declare-const a1 Int)
(declare-const a2 Int)
(declare-const a3 Int)
(declare-const a4 Int)
(declare-const a5 Int)
(declare-const a6 Int)

(define-fun I ((x Int) (y Int)) Bool
	(or (>= (+ (* a1 x) (* a2 y) a3) 0)
		(>= (+ (* a4 x) (* a5 y) a6) 0)))

(assert (or (not true) (forall ((y Int)) (I -50 y))))
(assert (forall ((x Int) (y Int)) (or (< y 0) (I (+ x y) (+ y 1)))))
(assert (forall ((x Int) (y Int)) (or (not (and (I x y) (>= x 0))) (> y 0))))

(check-sat)
(get-model)
