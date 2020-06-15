#lang racket
(require "parse.rkt"
         "anf.rkt"
         "cps.rkt"
         "optimize.rkt"
         "print-js.rkt"

         "ind-Exp.rkt")

(define (unparse e)
  (ind-Exp e
    (λ (id) (cond
              [(eqv? id 'exit) '(λ (v) v)]
              [else id]))
    (λ (datum) `(quote ,datum))
    (λ (f) `(call/cc ,f))
    (λ (x init body) `(let ([,x ,init]) ,body))
    (λ (x body) `(λ (,x) ,body))
    (λ (rator rand) `(,rator ,rand))
    (λ (v) `(inl ,v))
    (λ (v) `(inr ,v))
    (λ (tgt onl onr) `(which ,tgt ,onl ,onr))
    (λ (v) `(car ,v))
    (λ (v) `(cdr ,v))
    (λ (a d) `(cons ,a ,d))
    (λ (op rands) `(,op . ,rands))))


(define compile
  (compose print-js
           optimize
           cps
           anf
           parse))


#; ;; factorial 5
(compile '(let ([f (lambda (f)
                     (lambda (n)
                       (if (= n 0)
                           1
                           (* n ((f f) (- n 1))))))])
            ((f f) 5)))