#lang racket/base
(require racket/match
         racket/struct
         racket/list
         syntax/stx
         "context.rkt"
         "stx-util.rkt")
(provide (all-defined-out))

(module base racket/base
  (provide (all-defined-out))
  ;; List monad
  ;; type (M X) = (Listof X)
  (define (disj a b) (if (null? b) a (append a b)))
  (define return list)
  (define (bind1 c f) (for*/list ([x (in-list c)]) (f x)))
  (define (bind c f) (for*/list ([x (in-list c)] [y (in-list (f x))]) y))
  (define (fail) null)
  (define (to-list c) c))

#; ;; FIXME: this probably won't work with the new code structure...
(module base racket/base
  (provide (all-defined-out))
  ;; Maybe monad
  ;; type (M X) = X | #f -- X must not overlap with #f
  (define-syntax-rule (disj a b) (or a b))
  (define (return x) x)
  (define (bind1 c f) (if c (f c) #f))
  (define (bind c f) (if c (f c) #f))
  (define (fail) #f)
  (define (to-list c) (if c (list c) null)))

(module util racket/base
  (require racket/match)
  (require (submod ".." base))
  (provide (all-defined-out))
  ;; Monad syntax
  (define-syntax do
    (syntax-rules (<- =)
      [(_ ([p <- rhs] . rest) . body)
       (bind rhs (match-lambda [p (do rest . body)]))]
      [(_ ([p = rhs] . rest) . body)
       (match rhs [p (do rest . body)])]
      [(_ () . body) (let () . body)]))
  ;; Misc
  (define (stx? x) (or (syntax? x) (pair? x) (null? x))))

(require 'base 'util)

;; ----------------------------------------

;; In general, this file assumes that we only care about finding non-tainted
;; syntax. So it stops searching after seeing armed/tainted term.

;; path-append : Path Path -> Path
(define (path-append a b) (append a b))

;; stx-ref : Stx Path -> Syntaxish
(define (stx-ref stx path) (path-get stx path))

;; stx-seek : Stx Stx -> (M Path)
;; FIXME: vectors, structs, etc...
;; FIXME: assume at most one match, avoid general disj?
(define (stx-seek want in)
  (cond [(equal? want in) (return null)]
        [(and (syntax? in) (syntax-armed/tainted? in)) (fail)] ;; shortcut
        [(stx-pair? in)
         (disj (bind1 (stx-seek want (stx-car in)) path-add-car)
               (bind1 (stx-seek want (stx-cdr in)) path-add-cdr))]
        [else (fail)]))

;; ----------------------------------------

(define (vt? x) (or (vt:base? x) (vt:track? x) (vt:patch? x)))


;; A VT is one of
;; - (vt:base Stx Hash)             -- the term itself
;; - (vt:track Stx Stx VT Hash)     -- scope/arm/etc FROM, producing TO, within IN
;; - (vt:patch Path VT VT)          -- replace subterm at AT with TO, within IN
(struct vt:base (stx h) #;#:prefab
  #:property prop:custom-write
  (make-constructor-style-printer (lambda (self) 'vt:base)
                                  (match-lambda [(vt:base stx _) (list stx)])))
(struct vt:track (from to in h) #;#:prefab
  #:property prop:custom-write
  (make-constructor-style-printer (lambda (self) 'vt:track)
                                  (match-lambda [(vt:track from to in _) (list from to in)])))
(struct vt:patch (at to in) #:prefab)

(define (vt-depth vt)
  (match vt
    [(vt:track _ _ in _) (add1 (vt-depth in))]
    [(vt:patch p to in) (add1 (max (vt-depth to) (vt-depth in)))]
    [else 1]))

;; If vt ends in [e1->e2], and we want to search for e, then the naive approach
;; is to search for e in e2, fetch the corresponding (ie, same path) subterm of
;; e1, and continue searching for *that* term in the rest of vt. That is in fact
;; how we handle *rename* (ie, scope) changes. But if [e1->e2] is a disarm step,
;; then we cannot fetch a subterm from within the (armed) term e1. So we add the
;; path to a delayed *narrowing* and search for e1; once we find the pre-armed
;; version of e1, we apply the narrowing. Note that the search for e1 might
;; itself evolve through adjustments---that's fine.

;; vt-track : Stx Stx VT [Any] -> VT
(define (vt-track from to in [type #f])
  (cond [(eq? from to) in]
        [else (vt:track from to in (make-track-hash from to))]))

;; hash maps Syntax => (cons Stx Path)
(define (make-track-hash from to)
  (define h (make-hasheq))
  (define (loop to from rpath)
    (cond [(syntax? to)
           (hash-set! h to (cons from (reverse rpath)))
           (loop (syntax-e to) from rpath)]
          [(pair? to)
           (cond [(pair? from) ;; rpath = null
                  (loop (car to) (car from) rpath)
                  (loop (cdr to) (cdr from) rpath)]
                 [(and (syntax? from) (syntax-armed/tainted? from))
                  (loop (car to) from (path-add-car rpath))
                  (loop (cdr to) from (path-add-cdr rpath))]
                 [(syntax? from)
                  (loop to (syntax-e from) rpath)]
                 [else (error 'make-track-hash "mismatch: ~e, ~e" from to)])]
          ;; FIXME: vector, box, prefab
          [else (void)]))
  (begin (loop to from null) h))

;; vt-base : Stx -> Vt
(define (vt-base stx)
  (define h (make-hash))
  (let loop ([stx stx] [acc null])
    (cond [(syntax? stx)
           (hash-set! h stx (reverse acc))
           (unless (syntax-armed/tainted? stx)
             (loop (syntax-e stx) acc))]
          [(pair? stx)
           (hash-set! h stx (reverse acc)) ;; FIXME: store pairs too?
           (loop (car stx) (path-add-car acc))
           (loop (cdr stx) (path-add-cdr acc))]
          [else (void)]))
  (vt:base stx h))

;; vt-merge-at-path : Stx/VT Path VT -> VT
(define (vt-merge-at-path vt path sub-vt)
  (let ([sub-vt (if (stx? sub-vt) (vt-base sub-vt) sub-vt)])
    (cond [(equal? path null) sub-vt]
          [else (let ([vt (if (stx? vt) (vt-base vt) vt)])
                  (vt:patch path sub-vt vt))])))

;; ----------------------------------------

;; vt->stx : VT Path -> Stx
(define (vt->stx vt mask)
  (let loop ([vt vt] [mask mask])
    (match vt
      [(vt:base stx _)
       (path-get stx mask)]
      [(vt:track _ _ in _)
       (loop in mask)]
      [(vt:patch at to in)
       (cond [(path-cut-prefix at mask)
              => (lambda (mask*) (loop to mask*))]
             [else
              (define full (path-replace (loop in null) at (loop to null) #:resyntax? #f))
              (path-get full mask)])])))

;; ----------------------------------------

;; vt-seek : Stx VT Path -> (Listof Path)
;; The mask is removed from the prefix of each result; results that do not
;; extend the mask are discarded.
(define (vt-seek want vt mask)
  (filter list? (map (lambda (p) (path-cut-prefix mask p)) (to-list (seek1 want vt null)))))
(define (vt-seek/no-cut want vt mask)
  (filter (lambda (p) (path-prefix? mask p)) (to-list (seek1 want vt null))))

;; A Seeking is (seeking Stx Path) -- represents an intermediate search point.
(struct seeking (want narrow) #:prefab)

;; make-seeking : Stx Path -> Seeking
;; Discharges as much of the delayed narrowing as possible, then wraps in seeking.
(define (make-seeking want narrow)
  (define-values (want* narrow*)
    (path-get-until want narrow (lambda (x) (and (syntax? x) (syntax-armed/tainted? x)))))
  (seeking want* narrow*))

;; seek1 : Stx VT Path -> (M Path)
;; Find the path(s) of the NARROW subterm of WANT in VT. , then calls seek*.
(define (seek1 want vt [narrow null])
  (seek* (list (make-seeking want narrow)) vt))

;; seek* : Stx VT Path -> (M Path)
;; PRE: narrow is null or want is armed (or tainted)
(define (seek* ss vt)
  (define unique-ss (remove-duplicates ss))
  (match vt
    [(vt:base _ h)
     #;(eprintf "  ---- seek* on stx, ~s seekings, ~s unique\n" (length ss) (length unique-ss))
     ;; I think narrow could be non-empty here, if stx already had armed terms
     ;; and vt only tracked their disarming. (FIXME: test)
     (do ([(seeking want narrow) <- unique-ss])
         (cond [(hash-ref h want #f)
                => (lambda (path) (return (path-append path narrow)))]
               [else (fail)]))]
    [(vt:track from to in (? hash? h))
     ;; Possibilities:
     ;; - WANT is in TO (and corresponding subterm of FROM is in IN)
     ;; - WANT is in IN -- FIXME: add strict replacement flag?
     (define next-ss
       (disj (do ([(seeking want narrow) <- unique-ss])
                 (cond [(hash-ref h want #f)
                        => (match-lambda
                             [(cons want* narrow*)
                              (return (make-seeking want* (append narrow* narrow)))])]
                       [else (fail)]))
             unique-ss))
     (seek* next-ss in)]
    [(vt:track from to in _)
     ;; NOTE: unreachable case, left for comparison, history, etc
     ;; FIXME: untested...
     (define next-ss
       (disj (do ([(seeking want narrow) <- unique-ss]
                  [path1 <- (seek1 want to narrow)])
                 (return (make-seeking from (path-append path1 narrow))))
             unique-ss))
     (seek* next-ss in)]
    [(vt:patch at to in)
     ;; Possibilities:
     ;; - WANT is in TO
     ;; - WANT is in IN and no part of it is replaced
     ;; - WANT is in IN[AT:=TO] (but not IN) -- I think this is impossible in practice (???)
     ;;   or at least, we won't act on it unless that subterm has T honesty
     (disj (do ([p <- (seek* unique-ss in)])
               (if (path-prefix? at p) (fail) (return p)))
           (do ([p <- (seek* unique-ss to)])
               (return (path-append at p))))]))
