#lang racket/base
(require racket/match
         syntax/stx)
(provide path-add-ref
         path-add-tail
         path-add-car
         path-add-cdr
         path-get
         path-replace
         path-replacer)

;; A Path is a (list-of PathSeg), where the PathSegs are listed outermost to innermost.
;; For example: (path-get #'((a b) (c d)) (list (ref 0) (ref 1))) = #'b, not #'c

;; Paths are reversible (they can be built in accumulators), but as a consequence they
;; have non-canonical forms: for example, (list (ref 2)) = (list (tail 1) (ref 0)).

;; A PathSeg is one of
;; - Nat -- represents nth car
;; - NegativeInteger -- -(n+1) represents nth tail
(define (ref n) n)
(define (ref? x) (exact-nonnegative-integer? x))
(define (ref-n x) x)
(define (tail n) (- -1 n))
(define (tail? x) (and (exact-integer? x) (negative? x)))
(define (tail-n x) (sub1 (- x)))
(define (path-add-ref n p) (cons (ref n) p))
(define (path-add-tail n p)
  (match p
    [(cons (? tail t) p*) (cons (tail (+ n (tail-n t))) p*)]
    [_ (cons (tail n) p)]))
(define (path-add-car p) (path-add-ref 0 p))
(define (path-add-cdr p) (path-add-tail 0 p))

;; path-get : syntax Path -> syntax
(define (path-get stx path0)
  (let loop ([stx stx] [path path0])
    (cond [(null? path) stx]
          [(pair? path) (loop (pathseg-get stx (car path)) (cdr path))]
          [else (error 'path-get "bad path: ~s" path0)])))

;; pathseg-get : syntax PathSeg -> syntax
(define (pathseg-get stx0 path)
  (cond [(ref? path)
         (let loop ([n (ref-n path)] [stx stx0])
           (cond [(not (stx-pair? stx))
                  (error 'pathseg-get "path out of bounds: ~s, ~s" path stx0)]
                 [(zero? n) (stx-car stx)]
                 [else (loop (sub1 n) (stx-cdr stx))]))]
        [(tail? path)
         (let loop ([n (tail-n path)] [stx stx0])
           (cond [(not (stx-pair? stx))
                  (error 'pathseg-get "path out of bounds: ~s, ~s" path stx0)]
                 [(zero? n) (stx-cdr stx)]
                 [else (loop (sub1 n) (stx-cdr stx))]))]))

;; path-replace : Syntax Path Syntax [Boolean] -> syntax
(define (path-replace stx path x #:resyntax? [resyntax? #t])
  (cond [(null? path) x]
        [(pair? path)
         (let ([pathseg0 (car path)])
           (pathseg-replace stx
                            pathseg0
                            (path-replace (pathseg-get stx pathseg0)
                                          (cdr path)
                                          x
                                          resyntax?)
                            resyntax?))]
        [else (error 'path-replace "bad path: ~s" path)]))

;; pathseg-replace : Syntax PathSeg Syntax Boolean -> syntax
(define (pathseg-replace stx0 pathseg x resyntax?)
  (cond [(ref? pathseg)
         (let loop ([n (ref-n pathseg)] [stx stx0])
           (cond [(not (stx-pair? stx))
                  (error 'pathseg-replace "path out of bounds: ~s, ~s" pathseg stx0)]
                 [(zero? n) (stx-replcar stx x resyntax?)]
                 [else (stx-replcdr stx (loop (sub1 n) (stx-cdr stx)) resyntax?)]))]
        [(tail? pathseg)
         (let loop ([n (tail-n pathseg)] [stx stx0])
           (cond [(not (stx-pair? stx))
                  (error 'pathseg-replace "path out of bounds: ~s, ~s" pathseg stx0)]
                 [(zero? n) (stx-replcdr stx x resyntax?)]
                 [else (stx-replcdr stx (loop (sub1 n) (stx-cdr stx)) resyntax?)]))]))

;; stx-replcar : syntax syntax -> syntax
(define (stx-replcar stx x resyntax?)
  (cond [(pair? stx)
         (cons x (cdr stx))]
        [(and (syntax? stx) (pair? (syntax-e stx)))
         (let ([dstx (syntax-disarm stx #f)])
           (let ([result (cons x (cdr (syntax-e dstx)))])
             (if resyntax? (syntax-rearm (datum->syntax dstx result stx stx) stx) result)))]
        [else (raise-type-error 'stx-replcar "stx-pair" stx)]))

;; stx-replcdr : syntax syntax -> syntax
(define (stx-replcdr stx x resyntax?)
  (cond [(pair? stx)
         (cons (car stx) x)]
        [(and (syntax? stx) (pair? (syntax-e stx)))
         (let ([dstx (syntax-disarm stx #f)])
           (let ([result (cons (car (syntax-e dstx)) x)])
             (if resyntax? (syntax-rearm (datum->syntax dstx result stx stx) stx) result)))]
        [else (raise-type-error 'stx-replcdr "stx-pair" stx)]))

(define ((path-replacer stx path) s #:resyntax? [resyntax? #t])
  (path-replace stx path s #:resyntax? resyntax?))
