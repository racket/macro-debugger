#lang racket/base
(require racket/match
         syntax/stx
         "stx-util.rkt")
(provide path-add-ref
         path-add-tail
         path-add-car
         path-add-cdr
         path-get
         path-replace
         path-replacer)

;; A Path is a (list-of PathSeg), where the PathSegs are listed outermost to innermost.
;; For example: (path-get #'((a b) (c d)) '(car 1)) = #'(b), not #'(c d).

;; Paths are not reversible! (They cannot be build using accumulators.)
;; Paths have non-canonical forms: for example '(1 2 car) = '(list 3 car).

;; A PathSeg is one of
;; - 'car            -- represents nth car
;; - PositiveInteger -- -n represents nth tail (n cdrs, n>0)
(define (path-add-ref n p) (path-add-tail n (cons 'car p)))
(define (path-add-tail n p)
  (if (zero? n)
      p
      (match p
        [(cons (? exact-positive-integer? t) p*) (cons (+ n t) p*)]
        [_ (cons n p)])))
(define (path-add-car p) (cons 'car p))
(define (path-add-cdr p) (path-add-tail 1 p))

;; path-get : Stx Path -> Stx
(define (path-get stx path)
  (define (bad) (error 'path-get "out of bounds: ~s, ~e" path stx))
  (let loop ([stx stx] [path path])
    (match path
      ['() stx]
      [(cons 'car path)
       (if (stx-pair? stx) (loop (stx-car stx) path) (bad))]
      [(cons (? exact-positive-integer? n) path)
       (loop (for/fold ([stx stx]) ([_i (in-range n)])
               (if (stx-pair? stx) (stx-cdr stx) (bad)))
             path)])))

;; path-replace : Stx Path Stx [Boolean] -> Stx
(define (path-replace stx path x #:resyntax? [resyntax? #t])
  (define (bad) (error 'path-replace "out of bounds: ~s, ~e" path stx))
  (let loop ([stx stx] [path path])
    (match path
      ['() x]
      [(cons 'car path)
       (unless (stx-pair? stx) (bad))
       (stx-replcar stx (loop (stx-car stx) path) resyntax?)]
      [(cons (? exact-positive-integer? n) path)
       (let tailloop ([stx stx] [n n])
         (cond [(zero? n) (loop stx path)]
               [(not (stx-pair? stx)) (bad)]
               [else (stx-replcdr stx (tailloop (stx-cdr stx) (sub1 n)) resyntax?)]))])))

;; stx-replcar : syntax syntax -> syntax
(define (stx-replcar stx x resyntax?)
  (cond [(pair? stx)
         (cons x (cdr stx))]
        [(and (syntax? stx) (pair? (syntax-e stx)))
         (let ([dstx (stx-disarm stx)])
           (let ([result (cons x (cdr (syntax-e dstx)))])
             (if resyntax? (resyntax result stx dstx) result)))]
        [else (raise-type-error 'stx-replcar "stx-pair" stx)]))

;; stx-replcdr : syntax syntax -> syntax
(define (stx-replcdr stx x resyntax?)
  (cond [(pair? stx)
         (cons (car stx) x)]
        [(and (syntax? stx) (pair? (syntax-e stx)))
         (let ([dstx (stx-disarm stx)])
           (let ([result (cons (car (syntax-e dstx)) x)])
             (if resyntax? (resyntax result stx dstx) result)))]
        [else (raise-type-error 'stx-replcdr "stx-pair" stx)]))

(define ((path-replacer stx path) s #:resyntax? [resyntax? #t])
  (path-replace stx path s #:resyntax? resyntax?))
