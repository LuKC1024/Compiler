#lang racket
(provide parse)
(require "./ind-Exp.rkt")

(define (parse sexp)
  (match sexp
    [`,x #:when (symbol? x) (Var x)]
    [`(quote ,datum) (Quote datum)]
    [`(let ([,x ,init]) ,body) (Let x (parse init)
                                    (parse body))]
    [`(lambda (,x) ,body) (Lambda x (parse body))]
    [`(call/cc ,f) (Call/cc (parse f))]
    [`(inl ,v) (Inl (parse v))]
    [`(inr ,v) (Inr (parse v))]
    [`(which ,tgt ,onl ,onr) (Which (parse tgt)
                                    (parse onl)
                                    (parse onr))]
    [`(if ,cnd ,thn ,els) (Which (parse cnd)
                                 (Lambda '_ (parse thn))
                                 (Lambda '_ (parse els)))]
    [`(car ,v) (Car (parse v))]
    [`(cdr ,v) (Cdr (parse v))]
    [`(cons ,a ,d) (Cons (parse a) (parse d))]
    ;; base type
    [`,n #:when (integer? n) (Quote n)]
    [`(+ ,n ,m) (Delta '+ (list (parse n) (parse m)))]
    [`(- ,n ,m) (Delta '- (list (parse n) (parse m)))]
    [`(* ,n ,m) (Delta '* (list (parse n) (parse m)))]
    [`(/ ,n ,m) (Delta '/ (list (parse n) (parse m)))]
    [`(= ,n ,m) (Delta '= (list (parse n) (parse m)))]
    ;; application comes last
    [`(,rator ,rand) (Apply (parse rator) (parse rand))]))
