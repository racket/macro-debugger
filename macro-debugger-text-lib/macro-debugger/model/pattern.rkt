#lang racket/base
(require racket/match
         syntax/stx)
(provide (all-defined-out))

;; A Pattern is one of
;; - Symbol
;; - (cons Pattern Pattern)
;; - '()
;; - (rep Pattern VarList)
(struct rep (p vars) #:prefab)

;; A VarList is (Listof Symbol)

;; A Match is (cons VarList MatchEnv)
;; where MatchEnv = (Listof MatchValue)
;;       MatchValue = Stx | (Listof MatchValue)


;; parse-pattern : Sexpr -> Pattern
(define (parse-pattern p0)
  (let loop ([p p0])
    (match p
      ['() '()]
      [(? symbol? p) p]
      [(list p '...) (let ([p* (parse-pattern p)]) (rep p* (pattern-vars p)))]
      [(cons p1 p2) (cons (parse-pattern p1) (parse-pattern p2))]
      [_ (error 'parse-pattern "bad pattern: ~e in ~e" p p0)])))

;; pattern-vars : Pattern -> VarList
(define (pattern-vars p0)
  (let loop ([p p0])
    (match p
      [(? symbol? p) (list p)]
      [(cons p1 p2) (append (loop p1) (loop p2))]
      ['() null]
      [(rep p* vars*) vars*])))

;; pattern-match : Pattern Stx -> Match/#f
(define (pattern-match p0 t0)
  (define menv
    (let loop ([p p0] [t t0])
      (match p0
        [(? symbol? p) (list t)]
        ['() (and (stx-null? t0) null)]
        [(cons p1 p2)
         (cond [(stx-pair? t0)
                (let ([m1 (loop p1 (stx-car t0))]
                      [m2 (loop p2 (stx-cdr t0))])
                  (and m1 m2 (append m1 m2)))]
               [else #f])]
        [(rep p* vars*)
         (cond [(stx->list t0)
                => (lambda (ts)
                     (define ms (map (lambda (t) (loop p* t)) ts))
                     (and (andmap values ms)
                          (foldr (lambda (row acc) (map cons row acc))
                                 (map (lambda (var) null) vars*)
                                 ms)))]
               [else #f])])))
  (and menv (cons (pattern-vars p0) menv)))

;; pattern-template : Pattern Match -> Stx
(define (pattern-template p0 mv)
  (let outerloop ([p p0] [vars (car mv)] [m (cdr mv)])
    (define (var-index v)
      (or (for/first ([var (in-list vars)] [k (in-naturals)] #:when (eq? v var)) k)
          (error 'pattern-template "unknown var: ~e in ~e" v p)))
    (define (get-var v m) (list-ref m (var-index v)))
    (let loop ([p p0] [m m])
      (match p
        [(? symbol? p) (get-var p m)]
        ['() null]
        [(cons p1 p2) (cons (loop p1 m) (loop p2 m))]
        [(rep (? symbol? p) _) (get-var p m)]
        [(rep p* vars*)
         (define m* (map (lambda (v) (get-var v m)) m))
         (let reploop ([m* m*])
           (cond [(andmap pair? m*)
                  (cons (outerloop p* vars* (map car m*))
                        (reploop (map cdr m*)))]
                 [else null]))]))))

(define (pattern-resyntax p0 orig t0)
  (define (resyntax orig t) ;; note: no disarm, rearm
    (datum->syntax (syntax-disarm orig) t orig orig))
  (let loop ([p p0] [orig orig] [t t0])
    (if (or (syntax? t) (eq? t orig))
        t
        (match p
          [(cons p1 p2)
           (resyntax orig
                     (cons (loop p1 (stx-car orig) (car t))
                           (loop p2 (stx-cdr orig) (cdr t))))]
          [(rep p* _)
           (let reploop ([orig orig] [t t])
             (cond [(syntax? t) t]
                   [(stx-pair? t)
                    (resyntax orig
                              (cons (loop p* (stx-car orig) (stx-car t))
                                    (reploop (stx-cdr orig) (stx-cdr t))))]
                   [else (resyntax orig t)]))]
          [_ (resyntax orig t)]))))
