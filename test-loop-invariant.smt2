; Example from paper

;(define-fun x ()Int -50)

(declare-fun loopFuncX (Int Int) Int)
(declare-fun loopFuncY (Int Int) Int)

(assert (forall ((x Int) (y Int))
			(ite (< x 0) 
				(and (= (loopFuncX x y) (+ x y))
					 (= (loopFuncY x y) (+ y 1)))
				(> y 0))))

(check-sat)
(get-model)
