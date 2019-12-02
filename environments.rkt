#lang racket
(provide empty-env
         extend-env
         apply-env)

(define (empty-env) '())
(define (extend-env x v env)
  (cons (cons x v) env))
(define (apply-env env x)
  (cdr (assv x env)))