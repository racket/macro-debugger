#lang racket/base
(require racket/match
         syntax/stx
         "context.rkt"
         "stx-util.rkt")
(provide (all-defined-out))

#;
(module util racket/base
  (provide (all-defined-out))
  ;; List monad
  ;; type (M X) = (Listof X)
  (define-syntax do
    (syntax-rules (<- =)
      [(_ ([var <- rhs] . rest) . body)
       (bind rhs (lambda (var) (do rest . body)))]
      [(_ ([(var ...) = rhs] . rest) . body)
       (let-values ([(var ...) rhs]) (do rest . body))]
      [(_ () . body) (let () . body)]))
  (define (disj a b) (if (null? b) a (append a b)))
  (define return list)
  (define (bind1 c f) (for*/list ([x (in-list c)]) (f x)))
  (define (bind c f) (for*/list ([x (in-list c)] [y (in-list (f x))]) y))
  (define (fail) null)
  (define (to-list c) c)
  ;; Misc
  (define (stx? x) (or (syntax? x) (pair? x) (null? x))))

(module util racket/base
  (provide (all-defined-out))
  ;; Maybe monad
  ;; type (M X) = X | #f -- X must not overlap with #f
  (define-syntax do
    (syntax-rules (<- =)
      [(_ ([var <- rhs] . rest) . body)
       (bind rhs (lambda (var) (do rest . body)))]
      [(_ ([(var ...) = rhs] . rest) . body)
       (let-values ([(var ...) rhs]) (do rest . body))]
      [(_ () . body) (let () . body)]))
  (define-syntax-rule (disj a b) (or a b))
  (define (return x) x)
  (define (bind1 c f) (if c (f c) #f))
  (define (bind c f) (if c (f c) #f))
  (define (fail) #f)
  (define (to-list c) (if c (list c) null))
  ;; Misc
  (define (stx? x) (or (syntax? x) (pair? x) (null? x))))

(require 'util)

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

(require racket/struct)
;; A VT is one of
;; - Stx                            -- the term itself
;; - (vt:track Stx Stx VT Hash)     -- scope/arm/etc FROM, producing TO, within IN
;; - (vt:patch Path VT VT)          -- replace subterm at AT with TO, within IN
(struct vt:track (from to in h) #;#:prefab
  #:property prop:custom-write
  (make-constructor-style-printer (lambda (self) 'vt:track)
                                  (match-lambda [(vt:track from to in _) (list from to in)])))
(struct vt:patch (at to in) #:prefab)

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

;; vt-merge-at-path : VT Path VT -> VT
(define (vt-merge-at-path vt path sub-vt)
  (vt:patch path sub-vt vt))

;; ----------------------------------------

;; vt-seek : Stx VT Path -> (Listof Path)
;; The mask is removed from the prefix of each result; results that do not
;; extend the mask are discarded.
(define (vt-seek want vt mask)
  (filter list? (map (lambda (p) (path-cut-prefix mask p)) (to-list (seek want vt null)))))
(define (vt-seek/no-cut want vt mask)
  (filter (lambda (p) (path-prefix? mask p)) (to-list (seek want vt null))))

;; seek : Stx VT Path -> (M Path)
;; Find the path(s) of the NARROW subterm of WANT in VT. This function
;; discharges as much of the delayed narrowing as possible, then calls seek*.
(define (seek want vt [narrow null])
  (define-values (want* narrow*)
    (path-get-until want narrow (lambda (x) (and (syntax? x) (syntax-armed/tainted? x)))))
  (seek* want* vt narrow*))

;; seek* : Stx VT Path -> (M Path)
;; PRE: narrow is null or want is armed (or tainted)
(define (seek* want vt narrow)
  (match vt
    [(? stx? stx)
     ;; I think narrow could be non-empty here, if stx already had armed terms
     ;; and vt only tracked their disarming. (FIXME: test)
     (do ([path1 <- (stx-seek want stx)])
         (return (path-append path1 narrow)))]
    [(vt:track from to in (? hash? h))
     ;; Possibilities:
     ;; - WANT is in TO (and corresponding subterm of FROM is in IN)
     ;; - WANT is in IN -- FIXME: add strict replacement flag?
     (disj (cond [(hash-ref h want #f)
                  => (match-lambda
                       [(cons want* narrow*)
                        (seek want* in (append narrow* narrow))])]
                 [else (fail)])
           (seek want in narrow))]
    [(vt:track from to in _)
     ;; NOTE: unreachable case, left for comparison, history, etc
     (disj (do ([path1 <- (seek want to)]
                [path2 <- (seek from in (path-append path1 narrow))])
               (return path2))
           (seek want in narrow))]
    [(vt:patch at to in)
     ;; Possibilities:
     ;; - WANT is in TO
     ;; - WANT is in IN and no part of it is replaced
     ;; - WANT is in IN[AT:=TO] (but not IN) -- I think this is impossible in practice (???)
     (disj (do ([p <- (seek want in narrow)]
                [p <- (if (path-prefix? at p) (fail) (return p))])
               (return p))
           (bind1 (seek want to narrow) (lambda (path) (path-append at path))))]))
