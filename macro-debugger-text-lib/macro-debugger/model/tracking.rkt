#lang racket/base
(require racket/match
         syntax/stx
         "context.rkt"
         "stx-util.rkt")
(provide (all-defined-out))

(module util racket/base
  (provide (all-defined-out))
  ;; List monad
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

;; stx-seek : Stx Stx -> (Listof Path)
;; FIXME: vectors, structs, etc...
;; FIXME: assume at most one match, avoid general disj?
(define (stx-seek want in)
  (cond [(equal? want in) (return null)]
        [(and (syntax? in) (syntax-armed/tainted? in)) null] ;; shortcut
        [(stx-pair? in)
         (disj (bind1 (stx-seek want (stx-car in)) path-add-car)
               (bind1 (stx-seek want (stx-cdr in)) path-add-cdr))]
        [else null]))

;; ----------------------------------------

;; A VT is one of
;; - Stx                            -- the term itself
;; - (vt:track Stx Stx VT Any)      -- scope/arm/etc FROM, producing TO, within IN
;; - (vt:shallow Stx Stx VT Any)    -- shallow map FROM to TO, within IN
;; - (vt:patch Path VT VT)          -- replace subterm at AT with TO, within IN
(struct vt:track (from to in type) #:prefab)
(struct vt:shallow (from to in type) #:prefab)
(struct vt:patch (at to in) #:prefab)

;; If vt ends in [e1->e2], and we want to search for e, then the naive approach
;; is to search for e in e2, fetch the corresponding (ie, same path) subterm of
;; e1, and continue searching for *that* term in the rest of vt. That is in fact
;; how we handle *rename* (ie, scope) changes. But if [e1->e2] is a disarm step,
;; then we cannot fetch a subterm from within the (armed) term e1. So we add the
;; path to a delayed *narrowing* and search for e1; once we find the pre-armed
;; version of e1, we apply the narrowing. Note that the search for e1 might
;; itself evolve through adjustments---that's fine.

;; A vt:shallow node is an optimization for [e1->e2] where there's no point in
;; recursively searching through e2. For example, if (syntax-arm e1) -> e2, then
;; we can't search within e2. Or if (track-origin e1) -> e2, then the proper
;; subterms of e1 and e2 *might be* identical, in which case we might as well
;; just check e2 and then skip straight to the parent.

;; Note: (syntax-e (track-origin stx)) may or not be equal to (syntax-e stx); it
;; depends on whether stx's scopes have already been propagated. Likewise for
;; syntax-property.

;; vt-track : Stx Stx VT [Any] -> VT
(define (vt-track from to in [type #f])
  (cond [(eq? from to) in]
        [(and (syntax? to)
              (or (syntax-armed? to)
                  (equal? (syntax-e from) (syntax-e to))))
         (vt:shallow from to in type)]
        [else (vt:track from to in type)]))

;; ----------------------------------------

;; seek : Stx VT Path -> (Listof Path)
;; Find the path(s) of the NARROW subterm of WANT in VT. This function
;; discharges as much of the delayed narrowing as possible, then calls seek*.
(define (seek want vt [narrow null])
  (define-values (want* narrow*)
    (path-get-until want narrow (lambda (x) (and (syntax? x) (syntax-armed/tainted? x)))))
  (seek* want* vt narrow*))

;; seek* : Stx VT Path -> (Listof Path)
;; PRE: narrow is null or want is armed (or tainted)
(define (seek* want vt narrow)
  (match vt
    [(? stx? stx)
     ;; I think narrow could be non-empty here, if stx already had armed terms
     ;; and vt only tracked their disarming. (FIXME: test)
     (do ([path1 <- (stx-seek want stx)])
         (return (path-append path1 narrow)))]
    [(vt:track from to in _)
     ;; Possibilities:
     ;; - WANT is in TO (and corresponding subterm of FROM is in IN)
     ;; - WANT is in IN -- FIXME: add strict replacement flag?
     (disj (do ([path1 <- (seek want to)]
                [path2 <- (seek from in (path-append path1 narrow))])
               (return path2))
           (seek want in narrow))]
    [(vt:shallow from to in _)
     (disj (if (equal? want to) (seek from in narrow) null)
           (seek want in narrow))]
    [(vt:patch at to in)
     ;; Possibilities:
     ;; - WANT is in TO
     ;; - WANT is in IN and no part of it is replaced
     ;; - WANT is in IN[AT:=TO] (but not IN) -- I think this is impossible in practice (???)
     (disj (filter (lambda (p) (not (path-prefix? at p))) (seek want in narrow))
           (bind1 (seek want to narrow) (lambda (path) (path-append at path))))]))
