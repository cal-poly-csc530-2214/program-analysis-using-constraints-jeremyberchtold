#!/usr/bin/racket
#lang racket

(require rackunit)

(define (find-constraints x y)
	(+ x y))

(check-eq? (find-constraints '(set x 10)) (list (make-implication true '(I '((x 10))))))
(check-eq? (find-constraints '(ite (< x 0) (set x 1) (set x 2))) (list (make-implication '(< x 0) '(I '((x 1))))
																	   (make-implication '(>= x 0) '(I '((x 2))))))
(check-eq? (find-constraints '(ite (< x 0) (assert (< x -5)) (set x 2))) (list (make-implication '(< x 0) '(I '((x 1))))
																	   (make-implication '(>= x 0) '(I '((x 2))))))
