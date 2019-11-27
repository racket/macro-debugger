#lang racket/base
(require (for-syntax racket/base)
         racket/match
         syntax/stx
         "context.rkt"
         "stx-util.rkt")
(provide (all-defined-out))

(module base racket/base
  (require racket/match)
  (provide (struct-out rep)
           parse-pattern
           pattern-vars)

  ;; A Pattern is one of
  ;; - Symbol
  ;; - (cons Pattern Pattern)
  ;; - '()
  ;; - (rep Pattern VarList)
  ;; A VarList is (Listof Symbol)
  (struct rep (p vars) #:prefab)

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
        [(rep p* vars*) vars*]))))

(require (for-syntax 'base)
         (rename-in 'base [parse-pattern base:parse-pattern]))

(define-syntax (quote-pattern stx)
  (syntax-case stx ()
    [(_ p) #`(quote #,(parse-pattern (syntax->datum #'p)))]))

(define (parse-pattern p0)
  (hash-ref! pattern-cache p0 (lambda () (base:parse-pattern p0))))
(define pattern-cache (make-weak-hasheq))


;; A Match is (match-result VarList MatchEnv)
;; where MatchEnv = (Listof MatchValue)
;;       MatchValue = Stx | (Listof MatchValue)
(struct match-result (vars vals) #:prefab)
(define empty-match-result (match-result null null))

;; pattern-match : Pattern Stx -> Match/#f
(define (pattern-match p0 t0)
  (define menv
    (let loop ([p p0] [t t0])
      (match p
        [(? symbol? p) (list t)]
        ['() (and (stx-null? t) null)]
        [(cons p1 p2)
         (cond [(stx-pair? t)
                (let ([m1 (loop p1 (stx-car t))]
                      [m2 (loop p2 (stx-cdr t))])
                  (and m1 m2 (append m1 m2)))]
               [else #f])]
        [(rep p* vars*)
         (cond [(stx->list t)
                => (lambda (ts)
                     (define ms (map (lambda (t) (loop p* t)) ts))
                     (and (andmap values ms)
                          (foldr (lambda (row acc) (map cons row acc))
                                 (map (lambda (var) null) vars*)
                                 ms)))]
               [else #f])])))
  (and menv (match-result (pattern-vars p0) menv)))

;; pattern-match-update : Match Match [Nat/#f] -> Match
;; Updates first result with second. If index is given, then m2's vars
;; must occur in m1's pattern in ellipsis, and m2's values replace the
;; index-th elements rather than the whole lists.
(define (pattern-match-update m1 m2 [index #f])
  (match-define (match-result vars1 vals1) m1)
  (match-define (match-result vars2 vals2) m2)
  (define (m2-var-index v)
    (for/first ([var (in-list vars2)] [k (in-naturals)] #:when (eq? v var)) k))
  (define (list-replace xs k y)
    (cond [(not (pair? xs))
           (error 'pattern-match-update "index out of range: ~s for ~e" index m1)]
          [(zero? k) (cons y (cdr xs))]
          [else (cons (car xs) (list-replace (cdr xs) (sub1 k) y))]))
  (match-result vars1
                (for/list ([var (in-list vars1)] [val1 (in-list vals1)])
                  (cond [(m2-var-index var)
                         => (lambda (var-index2)
                              (define val2 (list-ref vals2 var-index2))
                              (cond [index (list-replace val1 index val2)]
                                    [else val2]))]
                        [else val1]))))

;; pattern-template : Pattern Match -> Stx
(define (pattern-template p0 mv)
  (match-define (match-result vars m) mv)
  (let outerloop ([p p0] [vars vars] [m m])
    (define (var-index v)
      (or (for/first ([var (in-list vars)] [k (in-naturals)] #:when (eq? v var)) k)
          (error 'pattern-template "unknown var: ~e in ~e" v p)))
    (define (get-var v m) (list-ref m (var-index v)))
    (let loop ([p p] [m m])
      (match p
        [(? symbol? p) (get-var p m)]
        ['() null]
        [(cons p1 p2) (cons (loop p1 m) (loop p2 m))]
        [(rep (? symbol? p) _) (get-var p m)]
        [(rep p* vars*)
         (define m* (map (lambda (v) (get-var v m)) vars*))
         (let reploop ([m* m*])
           (cond [(andmap pair? m*)
                  (cons (outerloop p* vars* (map car m*))
                        (reploop (map cdr m*)))]
                 [else null]))]))))

;; pattern-resyntax : Pattern Stx Stx -> Stx
(define (pattern-resyntax p0 orig t0)
  (let loop ([p p0] [orig orig] [t t0])
    (if (or (syntax? t) (eq? t orig))
        t
        (match p
          [(cons p1 p2)
           (restx (cons (loop p1 (stx-car orig) (car t))
                        (loop p2 (stx-cdr orig) (cdr t)))
                  orig)]
          [(rep p* _)
           (let reploop ([orig orig] [t t])
             (cond [(syntax? t) t]
                   [(stx-pair? t)
                    (restx (cons (loop p* (stx-car orig) (stx-car t))
                                 (reploop (stx-cdr orig) (stx-cdr t)))
                           orig)]
                   [else (restx t orig)]))]
          [_ (restx t orig)]))))

;; pattern-replace : Pattern Stx Pattern Stx -> Stx
;; Like (with-syntax ([p1 stx1]) (with-syntax ([p2 stx2]) (syntax p1))).
(define (pattern-replace p1 stx1 p2 stx2 #:resyntax? [resyntax? #t])
  (define m1 (pattern-match p1 stx1))
  (define m2 (pattern-match p2 stx2))
  (define m-out (pattern-match-update m1 m2))
  (define stx-out (pattern-template p1 m-out))
  (if resyntax? (pattern-resyntax p1 stx1 stx-out) stx-out))

;; subpattern-path : Pattern Symbol [Boolean] -> (U Path (vector Path Path))
;; FIXME: this allocates a lot for a search ...
(define (subpattern-path p0 hole [rep? #f])
  (or (let outerloop ([p p0] [rep? rep?])
        (let loop ([p p] [acc null])
          (match p
            [(cons p1 p2)
             (or (loop p1 (path-add-car acc))
                 (loop p2 (path-add-cdr acc)))]
            [(rep p* _)
             (cond [(outerloop p* #f)
                    => (lambda (subpath)
                         (if rep?
                             (vector (reverse acc) subpath)
                             (error 'subpattern->path "hole has ellipses: ~s, ~s" hole p0)))]
                   [else #f])]
            [(== hole)
             (when rep?
               (error 'subpattern->path "hole does not have ellipses: ~s, ~s" hole p0))
             (reverse acc)]
            [else #f])))
      (error 'subpattern->path "hole does not occur in pattern: ~s, ~s" hole p0)))
