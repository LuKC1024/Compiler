#lang racket

(define (empty-env) (hash))
(define (extend-env x v env) (hash-set env x v))
(define (apply-env env x) (hash-ref env x))

(define (mk-clos env x body)
  (lambda (arg)
    (valof body (extend-env x arg env))))
(define (app clos arg)
  (clos arg))

(struct inl (v) #:transparent)
(struct inr (v) #:transparent)
(define (which tgt dol dor)
  (match tgt
    [(inl v) (dol v)]
    [(inr v) (dor v)]))

(define (which-Result tgt datum clos either pair err)
  (case (car tgt)
    [(datum) datum]
    [(clos) clos]
    [(either) either]
    [(pair) pair]
    [(err) err]))

(define (type-error expected given)
  (λ (_)
    (error (format "Type Error: expecting ~a, given ~a"
                   expected given))))

(define (valof e env)
  (match e
    [`(call/cc ,f)
     (call/cc
       (λ (k)
         (cast (valof f env) => closure
           (λ (clos)
             (clos (: k Closure))))))]
    [`(var ,x) (apply-env env x)]
    [`(quote ,datum) (: datum Datum)]
    [`(lambda (,x) ,body) (: (mk-clos env x body) closure)]
    [`(apply ,rator ,rand)
     (cast (valof rator env) => closure
           (λ (clos)
             (clos rand)))]
    [`(inl ,u) (: (inl (valof u env)) either)]
    [`(inr ,u) (: (inr (valof u env)) either)]
    [`(which ,tgt ,dol ,dor)
     (cast (valof tgt env) => either
           (λ (tgt)
             (which tgt
               (λ (v)
                 (cast (valof dol) => closure
                       (λ (clos) (clos v))))
               (λ (v)
                 (cast (valof dor) => closure
                       (λ (clos) (clos v)))))))]
    [`(cons ,a ,d)
     (: (cons (valof a env) (valof d env)) pair)]
    [`(car ,pr) (cast (valof pr env) => pair
                      (λ (pr) (car pr)))]
    [`(cdr ,pr) (cast (valof pr env) => pair
                      (λ (pr) (cdr pr)))]))