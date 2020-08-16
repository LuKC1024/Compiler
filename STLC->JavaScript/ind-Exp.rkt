#lang racket
(provide (all-defined-out))

(struct Var (id) #:transparent)
(struct Quote (datum) #:transparent)
(struct Let (x init body) #:transparent)
(struct Lambda (x body) #:transparent)
(struct Apply (rator rand) #:transparent)
(struct Inl (v) #:transparent)
(struct Inr (v) #:transparent)
(struct Which (in onl onr) #:transparent)
(struct Car (v) #:transparent)
(struct Cdr (v) #:transparent)
(struct Cons (a d) #:transparent)
(struct Call/cc (f) #:transparent)
(struct Delta (op rands) #:transparent)

(define (ind-Exp e
                 onvar onquote
                 oncall/cc
                 onlet onlambda onapply
                 oninl oninr onwhich
                 oncar oncdr oncons ondelta)
  (let rec ([e e])
    (match e
      [(Var id) (onvar id)]
      [(Quote v) (onquote v)]
      [(Call/cc f) (oncall/cc (rec f))]
      [(Let x init body) (onlet x (rec init) (rec body))]
      [(Lambda x body) (onlambda x (rec body))]
      [(Apply rator rand) (onapply (rec rator) (rec rand))]
      [(Inl v) (oninl (rec v))]
      [(Inr v) (oninr (rec v))]
      [(Which tgt onl onr) (onwhich (rec tgt)
                                    (rec onl)
                                    (rec onr))]
      [(Car v) (oncar (rec v))]
      [(Cdr v) (oncdr (rec v))]
      [(Cons a d) (oncons (rec a) (rec d))]
      [(Delta op rands) (ondelta op (map rec rands))])))
