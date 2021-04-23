; Example from paper

(define-fun x () Int -50)

(define-fun loopFuncX ((x Int) (y Int)) Int (+ x y))
(define-fun loopFuncY ((x Int) (y Int)) Int (+ y 1))
(define-fun loopFun ((x Int) (y Int)) Bool
	(ite (< x 0)
		 (loopFun (+ x y) (+ y 1))
		 (> y 0)))

(declare-const y Int)
(assert (loopFun x y))

(check-sat)
(get-model)
