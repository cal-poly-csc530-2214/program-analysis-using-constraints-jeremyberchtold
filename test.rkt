#!/usr/bin/racket
#lang racket

(require rackunit)

;;;;;;;;;;;;;;;;;;;
;; Data Definitions
;;;;;;;;;;;;;;;;;;;


; An Implication is a representation of a mathematical logic implication consisting of:
;	- condition
;		The condition on the left side of this implication
;	- result
;		The result that should be true if the condition is true (if this implication holds)
(struct implication (condition result) #:transparent)


;;;;;;;;;;;;;;;;;;;;;;;
;; Function Definitions
;;;;;;;;;;;;;;;;;;;;;;;


;; invert-condition: Sexpr -> Sexpr
;; Returns the logical inverse of the given expression
(define (invert-condition c)
	(match c
		[(list '> var val) (list '<= var val)]
		[(list '< var val) (list '>= var val)]
		[(list '>= var val) (list '< var val)]
		[(list '<= var val) (list '> var val)]
		[else (error "Unsupported conditional")]))

(check-equal? (invert-condition '(> x 0)) '(<= x 0))
(check-equal? (invert-condition '(< y 2)) '(>= y 2))
(check-equal? (invert-condition '(>= z 17)) '(< z 17))
(check-equal? (invert-condition '(<= w -20)) '(> w -20))

;; add-implication-condition: Implication Sexpr
;; Adds a condition to the given implication
(define (add-implication-condition impl c)
	(if (eq? (implication-condition impl) 'true)
		(implication c (implication-result impl))
		(implication (list 'or c (implication-condition impl)) (implication-result impl))))

(check-equal? (add-implication-condition (implication 'true '(I ((x 10)))) '(< x 10))
		   (implication '(< x 10) '(I ((x 10)))))
(check-equal? (add-implication-condition (implication '(> x 15) '(I ((x 0)))) '(< x 5))
		   (implication '(or (< x 5) (> x 15)) '(I ((x 0)))))
(check-equal? (add-implication-condition (implication '(or (< x 5) (> x 15)) '(I ((x 0)))) '(< x 2))
		   (implication '(or (< x 2) (or (< x 5) (> x 15))) '(I ((x 0)))))

;; find-constraints: Sexpr -> Listof[Implication]
;; Finds the invariant constraints for a given Sexpr that represents code in an imperative language (with while-loops, etc.)
(define (find-constraints expr)
	(match expr
		[(list 'set var val) (list (implication 'true (list 'I (list (list var val)))))]
		[(list 'assert expr) (list (implication 'true expr))]
		[(list 'ite condition iftrue iffalse) (append (map (lambda (constraint) (add-implication-condition constraint condition)) (find-constraints iftrue))
													  (map (lambda (constraint) (add-implication-condition constraint (invert-condition condition))) (find-constraints iffalse)))]
		[(list 'while condition loop afterloop) (append (map (lambda (constraint) (add-implication-condition constraint condition)) (find-constraints loop))
														(map (lambda (constraint) (add-implication-condition constraint (invert-condition condition))) (find-constraints afterloop)))]
		[(list (list _ ...) ...) (flatten (map find-constraints expr))]
		[else (error "Unsupported operation")]))

(check-equal? (find-constraints '(set x 10)) (list (implication 'true '(I ((x 10))))))
(check-equal? (find-constraints '(ite (< x 0) (set x 1) (set x 2))) (list (implication '(< x 0) '(I ((x 1))))
																	   (implication '(>= x 0) '(I ((x 2))))))
(check-equal? (find-constraints '(ite (< x 0) (assert (< x -5)) (set x 2))) (list (implication '(< x 0) '(< x -5))
																	   			  (implication '(>= x 0) '(I ((x 2))))))
(check-equal? (find-constraints '(while (< x 0) (set x 1) (set x 2))) (list (implication '(< x 0) '(I ((x 1))))
																	   (implication '(>= x 0) '(I ((x 2))))))
(check-equal? (find-constraints '((set x 10) (while (>= x 0) (set x (- x 1)) (assert (< x 0)))))
	(list (implication 'true '(I ((x 10))))
		  (implication '(>= x 0) '(I ((x (- x 1)))))
		  (implication '(< x 0) '(< x 0))))
