#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         racket/stxparam
         racket/contract/base
         racket/list
         syntax/stx
         racket/match
         racket/pretty
         "deriv-util.rkt"
         "stx-util.rkt"
         "pattern.rkt"
         "context.rkt"
         "tracking.rkt"
         "steps.rkt")

(provide STRICT-CHECKS
         DEBUG)

(define-syntax-rule (STRICT-CHECKS form ...)
  (when #f form ... (void)))

(define-syntax-rule (DEBUG form ...)
  (when #t form ... (void)))

(define (hash-set-list h ks v)
  (for/fold ([h h]) ([k (in-list ks)]) (hash-set h k v)))
(define (hash-remove-list h ks)
  (for/fold ([h h]) ([k (in-list ks)]) (hash-remove h k)))

(define state/c (or/c state? #f))

;; ============================================================
;; Hiding configuration

(provide
 (contract-out
  [macro-policy (parameter/c (-> identifier? any/c))]))

(define macro-policy (make-parameter (lambda (id) #t)))

;; ============================================================
;; Expansion Context

(provide
 (contract-out
  [the-phase (parameter/c exact-nonnegative-integer?)]
  [the-context (parameter/c list?)]
  [the-big-context (parameter/c (listof bigframe?))]
  [call-with-initial-context (-> (-> any) #:xstate xstate? any)])
 honest?)

(define the-phase (make-parameter 0))
(define the-context (make-parameter null))
(define the-big-context (make-parameter null))

(define the-vt (make-parameter #f))         ;; (Parameterof VT)
(define the-vt-mask (make-parameter null))  ;; (Parameterof Path)
(define honesty (make-parameter 'T))        ;; (Parameterof HonestyMask)

(define (call-with-initial-context proc #:xstate xst)
  (parameterize ((the-xstate xst)
                 (the-phase 0)
                 (the-context null)
                 (the-big-context null)
                 (the-vt #f)
                 (the-vt-mask null)
                 (honesty 'T))
    (proc)))

;; set-honesty : HonestyMask Stx -> Void
;; PRE: hm <= (honesty) -- that is, honesty is only decreased or left unchanged
;; Invariant: (honesty) = 'T  iff  (the-vt) = #f
(define (set-honesty hm f)
  (DEBUG (unless (eq? (honesty) hm) (eprintf "set-honesty : ~s => ~s\n" (honesty) hm)))
  (when (eq? (honesty) 'T) (the-vt (vt-base f)))
  (honesty hm))

;; honest? : -> Boolean
(define (honest?) (eq? (honesty) 'T))

;; not-complete-fiction? : -> Boolean
(define (not-complete-fiction?) (not (eq? (honesty) 'F)))

;; ============================================================
;; Expansion State

(provide
 (struct-out xstate)
 (contract-out
  [the-xstate (parameter/c (or/c xstate? #f))]
  [new-xstate (-> xstate?)]
  [next-seqno (-> exact-nonnegative-integer?)]
  [add-step (-> protostep? void?)])
 ;; FIXME
 learn-binders 
 learn-definites
 add-lift
 add-endlift
 get/clear-lifts
 get/clear-endlifts)

;; An XState is:
(struct xstate
  (seqno        ;; Nat
   binders      ;; ImmutableHasheq[Identifier => Phase]
   definites    ;; ImmutableHasheq[Identifier => Phase]
   lifts        ;; (Listof Lift)
   endlifts     ;; (Listof Syntax)
   frontier     ;; ImmutableHashEq[Syntax => #t]
   steps        ;; ReductionSequence
   ) #:transparent #:mutable)
;; where Lift = (list 'def Ids Syntax) | (list 'req Syntax) | (list 'mod Syntax)

;; the-xstate : (Parameterof XState/#f)
(define the-xstate (make-parameter #f))

;; new-xstate : -> XState
(define (new-xstate)
  (xstate 0 '#hasheq() '#hasheq() null null '#hasheq() null))

;; next-seqno : -> Nat
(define (next-seqno #:xstate [xst (the-xstate)])
  (let ([n (xstate-seqno xst)]) (set-xstate-seqno! xst (add1 n)) n))

;; learn-{binders,definites} : Id/s -> Void
(define (learn-binders ids #:xstate [xst (the-xstate)])
  (set-xstate-binders! xst (hash-set-list (xstate-binders xst) (flatten-identifiers ids) (the-phase))))
(define (learn-definites ids #:xstate [xst (the-xstate)])
  (set-xstate-definites! xst (hash-set-list (xstate-definites xst) (flatten ids) (the-phase))))

;; add-lift : Lift -> Void
;; add-endlift : Syntax -> Void
(define (add-lift lift #:xstate [xst (the-xstate)])
  (set-xstate-lifts! xst (cons lift (xstate-lifts xst))))
(define (add-endlift lift #:xstate [xst (the-xstate)])
  (set-xstate-endlifts! xst (cons lift (xstate-endlifts xst))))

;; get/clear-lifts : -> (Listof Lift)
;; get/clear-endlifts : -> (Listof Syntax)
(define (get/clear-lifts #:xstate [xst (the-xstate)])
  (set-xstate-lifts! xst null))
(define (get/clear-endlifts #:xstate [xst (the-xstate)])
  (set-xstate-endlifts! xst null))

;; add-step : Step -> Void
(define (add-step step) (when (honest?) (do-add-step step)))
(define (do-add-step step #:xstate [xst (the-xstate)])
  (set-xstate-steps! xst (cons step (xstate-steps xst))))

;; ============================================================
;; Creating steps

(provide
 (contract-out
  [current-state-with
   (-> syntaxish? syntaxish?
       state?)]
  [walk
   (->* [syntaxish? syntaxish? step-type?]
        [#:foci1 syntaxish? #:foci2 syntaxish?]
        step?)]
  [stumble
   (->* [syntaxish? exn?]
        [#:focus syntaxish?]
        misstep?)]
  [walk/talk
   (-> step-type? (listof (or/c syntax? string? 'arrow))
       protostep?)]
  [foci
   (-> any/c (listof syntax?))]))

(define (current-state-with e fs)
  (define xst (the-xstate))
  (make state e (foci fs) (the-context) (the-big-context)
        (xstate-binders xst) (xstate-definites xst)
        (xstate-frontier xst) (xstate-seqno xst)))

(define (walk e1 e2 type
              #:foci1 [foci1 e1]
              #:foci2 [foci2 e2])
  (make step type
        (current-state-with e1 foci1)
        (current-state-with e2 foci2)))

(define (stumble stx exn #:focus [focus stx])
  (make misstep 'error (current-state-with stx focus) exn))

(define (walk/talk type contents)
  (make remarkstep type (current-state-with #f null) contents))

(define (foci x) (filter syntax? (flatten x)))


;; ============================================================
;; RS: the reduction state monad

(provide
 RS/c
 (contract-out
  [RSunit
   (-> syntaxish? syntaxish? pattern/c state/c RS/c)]
  [RSfail
   (-> exn? RS/c)]
  [RSbind
   (-> RS/c (-> any/c any/c state/c RS/c) RS/c)]
  [RScase
   (-> RS/c
       (-> any/c any/c any/c state/c any)
       (-> exn? any)
       any)]
  [RSreset
   (->* [RS/c] [#:pattern (or/c pattern/c #f)] RS/c)]))

;; RS = (rsok Stx Stx Pattern State)
;;    | (rsfailed Exn)
(struct rsok (f v p s))
(struct rsfailed (exn))

(define RS/c (or/c rsok? rsfailed?))

(define pattern/c any/c) ;; FIXME?

(define RST/c
  ;; First two args are any/c instead of syntaxish? because of
  ;; #:new-local-context that initially sets syntax to #f.
  (-> (or/c syntaxish? #f) (or/c syntaxish? #f) pattern/c state/c
      RS/c))

(define (RSunit f v p s) (rsok f v p s))
(define (RSfail exn) (rsfailed exn))

(define (RSbind a fun)
  (match a
    [(rsok f v p s) (fun f v p s)]
    [(rsfailed exn) a]))

(define (RScase a ok fail)
  (match a
    [(rsok f v p s) (ok f v p s)]
    [(rsfailed exn) (fail exn)]))

(define (RSreset a #:pattern [reset-p #f])
  (RSbind a (lambda (f v p s) (RSunit f v (or reset-p p) s))))


;; ============================================================
;; Implicit match from #:pattern

(provide % %e)

(define-syntax-parameter the-match-result
  (lambda (stx)
    (raise-syntax-error #f "no match result; used outside of with-pattern-match" stx)))

(define-syntax-rule (% p) (%e (quote-template-pattern p)))
(define-syntax-rule (%e p) (pattern-template p the-match-result))

(define-syntax with-pattern-match
  (syntax-parser
    [(_ [f p] expr:expr)
     #'(let ([mv (pattern-match p f)])
         (syntax-parameterize ((the-match-result (make-rename-transformer #'mv)))
           expr))]))


;; ============================================================

(provide R !)

(define-syntax ! (syntax-rules ()))

;; (R R-clause ...) : RST
(begin-for-syntax
  (define clause-kw->macro
    (hash '#:set-syntax #'R/set-syntax
          '#:pattern #'R/pattern
          '#:do #'R/do
          '#:let #'R/let
          '#:parameterize #'R/parameterize
          '#:walk #'R/walk
          '#:rename #'R/rename
          '#:rename/mark #'R/rename/mark
          '#:rename/unmark #'R/rename/unmark
          '#:with-marking #'R/with-marking
          '#:new-local-context #'R/new-local-context
          '#:if #'R/if
          '#:when #'R/when
          '#:pass1 #'R/pass1
          '#:pass2 #'R/pass2
          '#:in-hole #'R/in-hole
          '#:hide-check #'R/hide-check
          '#:seek-check #'R/seek-check
          ))

  (define-syntax-class RClause #:attributes (macro)
    #:literals (!)
    (pattern [! . _]
             #:with macro #'R/!)
    (pattern [e:expr . _]
             #:with macro #'R/run)
    (pattern [kw:keyword . _]
             #:attr macro (hash-ref clause-kw->macro (syntax-e #'kw) #f)
             #:fail-when (and (not (attribute macro)) #'kw) "unknown keyword")))

;; syntax (R RClause ...) : RST
(define-syntax-rule (R . clauses)
  (lambda (f v p s) (R** f v p s . clauses)))

;; syntax (R** f v p s RClause ...) : RS
(define-syntax R**
  (syntax-parser
    #:literals (=>)
    [(R** f v p s)
     #'(RSunit f v p s)]
    [(R** f v p s => k . more)
     #:declare k (expr/c #'RST/c)
     #'(RSbind (RSreset (k.c f v p s) #:pattern p)
               (R . more))]
    [(R** f v p s c:RClause . more)
     #'(begin
         (DEBUG
          (let ([cstx (quote-syntax c)])
            (define where (format "[~s:~s]" (syntax-line cstx) (syntax-column cstx)))
            (eprintf "doing ~a ~.s, honesty = ~s, v = ~.s\n"
                     where (trim-quoted-clause (quote c)) (honesty) (stx->datum v))))
         (c.macro f v p s c (R . more)))]))

(define (trim-quoted-clause c)
  (match c [(cons (and kw (or '#:parameterize #:when #:if #:with-marking #:do)) _) `(,kw _)] [_ c]))

;; A R/<Clause> macro has the form
;;   (R/<Clause> f v p s <Clause> kexpr)
;; where f,v,p,w,ws are *variables* and kexpr is *expression*
;; - f is the "real" form
;; - v is the "virtual/visible" form (used for steps)
;; - p is the current pattern
;; - s is the last marked state, or #f
;; - kexpr is the continuation (RST)

(define-syntax R/!
  (syntax-parser
    #:literals (!)
    ;; Error-point case
    [(_ f v p s [! maybe-exn] ke)
     #:declare maybe-exn (expr/c #'(or/c exn? #f))
     #'(let ([x maybe-exn.c])
         (if x
             (begin (do-add-step (stumble v x))
                    (RSfail x))
             (ke f v p s)))]))

(define-syntax R/pattern
  (syntax-parser
    ;; Change patterns
    [(_ f v p s [#:pattern p2] ke)
     #'(ke f v (quote-pattern p2) s)]))

(define-syntax R/do
  (syntax-parser
    ;; Execute expressions for effect
    [(_ f v p s [#:do expr ...] ke)
     #'(begin
         (with-pattern-match [f p] (let () expr ... (void)))
         (ke f v p s))]))

(define-syntax R/let
  (syntax-parser
    [(_ f v p s [#:let var:id expr] ke)
     #'(let ([var (with-pattern-match [f p] expr)])
         (ke f v p s))]))

(define-syntax R/parameterize
  (syntax-parser
    [(_ f v p s [#:parameterize ((param expr) ...) . clauses] ke)
     #:declare param (expr/c #'parameter?)
     #'(RSbind (parameterize ((param.c (with-pattern-match [f p] expr)) ...)
                 (R** f v p s . clauses))
               ke)]))

;; FIXME: WHEN?
(define-syntax R/set-syntax
  (syntax-parser
    ;; Change syntax
    [(_ f v p s [#:set-syntax form] ke)
     #:declare form (expr/c #'syntaxish?)
     #'(let ([f2 (with-pattern-match [f p] form.c)])
         (ke f2 (change-visible-term f f2 v) p s))]))

(define (change-visible-term f f2 v)
  (cond [(honest?) f2]
        [else (set-honesty 'F f) v]))

(begin-for-syntax
  (define-syntax-class walk-clause
    #:attributes (state1.c form1.c form2.c foci1.c foci2.c type)
    (pattern [#:walk form2 type:expr
              (~alt (~optional (~seq #:foci foci2))
                    (~optional (~seq #:from-state state1))
                    (~optional (~seq #:from form1))
                    (~optional (~seq #:from-foci foci1))) ...]
             #:declare state1 (expr/c #'state/c)
             #:declare form1 (expr/c #'syntaxish?)
             #:declare foci1 (expr/c #'syntaxish?)
             #:declare form2 (expr/c #'syntaxish?)
             #:declare foci2 (expr/c #'syntaxish?))))

(define-syntax R/walk
  (syntax-parser
    [(_ f v p s w:walk-clause ke)
     #'(let ()
         (define-values (state1 f1 f2 type)
           (with-pattern-match [f p]
             (values (~? w.state1.c #f) (~? w.form1.c v) w.form2.c w.type)))
         (define-values (fs1 fs2)
           (with-pattern-match [f p]
             (values (~? w.foci1.c f1) (~? w.foci2.c f2))))
         (do-walk f v p s state1 f1 fs1 f2 fs2 type ke))]))

(define (do-walk f v p s state1 f1 fs1 f2 fs2 type k)
  (define s1 (or state1 (current-state-with f1 fs1)))
  (define s2 (current-state-with f2 fs2))
  (when (and type (honest?))
    (do-add-step (make step type s1 s2)))
  (k f2 (change-visible-term f f2 v) p s2))

(define-syntax R/rename
  (syntax-parser
    ;; Rename
    [(_ f v p s [#:rename pattern renames] ke)
     #'(RSbind (Rename f v p s pattern renames #f #f) ke)]
    [(_ f v p s [#:rename pattern renames description] ke)
     #'(RSbind (Rename f v p s pattern renames description #f) ke)]))

(define-syntax-rule (Rename f v p s pattern renames description mark-flag)
  (let ()
    (define-values (renames-var description-var)
      (with-pattern-match [f p] (values renames description)))
    (do-rename f v p s (quote-pattern pattern) renames-var description-var mark-flag)))

(define (do-rename f v p s ren-p renames description mode)
  (DEBUG
   (eprintf "do-rename(~s): ~.s at ~s\n" (or mode description) (stx->datum renames) ren-p)
   (eprintf "  v = ~.s\n" (stx->datum v)))
  (define pre-renames (pattern-template ren-p (pattern-match p f)))
  (define f2 (pattern-replace p f ren-p renames))
  #;(DEBUG (eprintf "  renamed: f-diff = ~s / ~s\n" (stx-eq-diff f f2) (stx-eq-diff f2 f)))
  ;; renaming preserves honesty
  (when (the-vt) (the-vt (vt-track pre-renames renames (the-vt) description)))
  ;; ----
  ;; Note: renames might have more structure than pre-renames, especially if arming!
  (define-values (v2 foci1 foci2)
    (cond [(honest?)
           (values (pattern-replace p f ren-p renames #:resyntax? #t)
                   pre-renames renames)]
          [(eq? mode 'mark)
           ;; FIXME: if honesty = (T . F), then what about mark visibility?
           ;; FIXME: if mode is mark or unmark, should honesty be strictly 'T or 'F ??
           (values v null null)]
          [else
           (define-values (v2 foci1 foci2)
             (do-rename-v v (the-vt) (the-vt-mask) (honesty) pre-renames renames))
           (values (honesty-composite (honesty) f2 v2)
                   ;; Must include pre-renames,renames for true part (FIXME: need narrowing?)
                   (cons foci1 pre-renames) (cons foci2 renames))]))
  (DEBUG (eprintf "  renamed: diff=~s, v2 = ~.s \n" (stx-eq-diff v2 v) (stx->datum v2)))
  (when (and (not (memq description '(#f sync)))
             (not-complete-fiction?))
    ;; FIXME: better condition/heuristic for when to add rename step?
    (do-add-step (walk v v2 description #:foci1 foci1 #:foci2 foci2)))
  (RSunit f2 v2 p s))

(define (honesty-composite hm f v #:resyntax? [resyntax? #t])
  (DEBUG (eprintf "honesty-composite: ~s\n f = ~.s\n v = ~.s\n" hm f v))
  (let loop ([hm hm] [f f] [v v])
    (match hm
      ['T f]
      ['F v]
      [(cons hma hmb)
       (define c (cons (loop hma (stx-car f) (stx-car v))
                       (loop hmb (stx-cdr f) (stx-cdr v))))
       (if resyntax? (restx c v) c)])))

(define (do-rename-v v vt vt-mask hm pre post)
  (DEBUG
   (eprintf " do-rename-v, mask=~s, vt depth = ~s\n" vt-mask (vt-depth vt))
   (eprintf "  vt-stx = ~.s\n" (stx->datum (vt->stx vt vt-mask)))
   #;(begin (eprintf "   vt = " vt-mask) (pretty-print vt) (eprintf "\n")))
  ;; fictional-subvs is a hash (set) containing all fictional subterms of v
  (define fictional-subvs (make-hash))
  (let loop ([hm hm] [v (stx->datum v)])
    (match hm
      ['F (let floop ([v v])
            (hash-set! fictional-subvs v #t)
            (when (pair? v) (floop (car v)) (floop (cdr v))))]
      ['T (void)]
      [(cons hma hmb) (loop hma (car v)) (loop hmb (cdr v))]))
  ;; Recur through pre,post to find the largest sub-renames that apply to v.
  ;; Use fictional-subvs to prune the search (if pre-d not in fictional-subvs, can skip).
  (define (init-k v accren) (values v (map car accren) (map cdr accren)))
  (let loop ([pre pre] [post post] [pre-d (stx->datum pre)] [v v] [accren null] [k init-k])
    (define (try-rename)
      (cond [(null? pre) #f] ;; FIXME: generalize
            [(hash-ref fictional-subvs pre-d #f)
             (match (vt-seek pre vt vt-mask)
               [(cons path _)
                (DEBUG
                 (eprintf "  found at ~s, pre = ~.s\n" path (stx->datum pre))
                 (with-handlers ([exn?
                                  (lambda (e)
                                    (eprintf "** vt-mask = ~s, vt = \n" vt-mask)
                                    (parameterize ((pretty-print-columns 160))
                                      (pretty-print vt))
                                    (eprintf "\n")
                                    (raise e))])
                   (eprintf "    actually = ~.s\n" (stx->datum (path-get v path))))
                 (eprintf "  do-rename-v : replace at ~s : ~.s => ~.s\n"
                          path (stx->datum v) (stx->datum (path-replace v path post))))
                (cons (path-replace v path post #:resyntax? #t)
                      (cons (cons pre post) accren))]
               [else #f])]
            [else #f]))
    (cond [(try-rename) => (match-lambda [(cons v accren) (k v accren)])]
          [(pair? pre-d)
           (loop (stx-car pre) (stx-car post) (car pre-d) v accren
                 (lambda (v accren)
                   (loop (stx-cdr pre) (stx-cdr post) (cdr pre-d) v accren k)))]
          [else (k v accren)])))

(define-syntax R/rename/mark
  (syntax-parser
    [(_ f v p s [#:rename/mark pvar to] ke)
     #:declare to (expr/c #'syntaxish?)
     #'(RSbind (Rename f v p s pvar to.c #f 'mark) ke)]))

(define-syntax R/rename/unmark
  (syntax-parser
    [(_ f v p s [#:rename/unmark pvar to] ke)
     #:declare to (expr/c #'syntaxish?)
     #'(RSbind (Rename f v p s pvar to.c #f 'unmark) ke)]))

;; - corresponds to the dynamic extent of a syntax-local-introduce bindings
;; - used to delay mark, to keep visible syntax unmarked
(define-syntax-rule (R/with-marking f v p s [#:with-marking c ...] ke)
  (RSbind (do-marking f v p s (R c ...)) ke))

(define (do-marking f v p s rst)
  (parameterize ((marking-table (if (honest?) #f (make-renames-mapping null null))))
    (rst f v p s)))

;; What if honesty is all we need?
;; hide = (set-honesty 'F _)
;; seek = ...


(define-syntax R/if
  (syntax-parser
    ;; Conditional (pattern changes lost afterwards ...) ;; FIXME???
    [(_ f v p s [#:if test [consequent ...] [alternate ...]] ke)
     #'(RSbind (RSreset (if (with-pattern-match [f p] test)
                            (R** f v p s consequent ...)
                            (R** f v p s alternate ...))
                        #:pattern p)
               ke)]))

(define-syntax R/when
  (syntax-parser
    ;; Conditional (pattern changes lost afterwards ...) ;; FIXME???
    [(_ f v p s [#:when test consequent ...] ke)
     #'(R/if f v p s [#:if test [consequent ...] []] ke)]))


;; ** Multi-pass reductions **

;; Pass1 does expansion.
;; If something should happen regardless of whether hiding occurred
;; in pass1 (eg, lifting), put it before the Pass2 marker.

;; Use #:unsafe-bind-visible to access 'v'
;; Warning: don't do anything that relies on real 'f' before pass2

;; If something should be hidden if any hiding occurred in pass1,
;; put it after the Pass2 marker (eg, splice, block->letrec).

(define-syntax R/pass1
  (syntax-parser
    [(_ f v p s [#:pass1] ke)
     #'(ke f v p s)]))

(define-syntax R/pass2
  (syntax-parser
    [(_ f v p s [#:pass2 clause ...] ke)
     #'(ke f v p s)]))

(define-syntax R/new-local-context
  (syntax-parser
    [(_ f v p s [#:new-local-context clause ...] ke)
     #'(do-local-context f v p s (R clause ...) ke)]))

(define (do-local-context f v p s rst k)
  (cond [(honest?)
         (RSbind (call/local-context v (lambda () (rst #f #f (quote-pattern _) #f)))
                 (lambda (_f2 _v2 _p2 _s2)
                   (k f v p s)))]
        [else
         (RSbind (rst #f v (quote-pattern _) #f)
                 (lambda (_f2 v2 _p2 _s2)
                   (k f v2 p s)))]))

(define (call/local-context v proc)
  (define bf (bigframe (the-context) (list v) v))
  (parameterize ((the-big-context (cons bf (the-big-context))))
    (proc)))

(define-syntax R/run
  (syntax-parser
    ;; Subterm handling
    [(R** f v p s [reducer hole fill] ke)
     #:declare reducer (expr/c #'(-> any/c RST/c))
     #'(RSbind (run reducer.c f v p s (quote hole) fill)
               ke)]))

;; FIXME: should this be used more?
(define-syntax R/in-hole
  (syntax-parser
    [(_ f v p s [#:in-hole hole . clauses] ke)
     #'(RSbind (let ([reducer (lambda (_) (R . clauses))])
                 (run reducer f v p s (quote hole) #f))
               ke)]))

;; ============================================================

(define-syntax R/hide-check
  (syntax-parser
   [(_ f v p s [#:hide-check rs] ke)
    #:declare rs (expr/c #'(listof identifier?))
    #'(do-hide-check f v p s (with-pattern-match [f p] rs.c) ke)]))

(define (do-hide-check f v p s ids k)
  (unless (or (eq? (honesty) 'F) (andmap (macro-policy) ids))
    (DEBUG
     (eprintf "hide-check: hiding with f=~.s, v=~.s\n" (stx->datum f) (stx->datum v)))
    ;; FIXME: marking-table ???
    ;; FIXME: set-honesty needs to rebuild table if honesty strictly *decreases*
    (set-honesty 'F f))
  (k f v p s))

(define-syntax-rule (R/seek-check f v p s [#:seek-check] ke)
  (do-seek-check f v p s ke))

(define (do-seek-check f v p s k)
  (cond [(honest?) (k f v p s)]
        [else
         (match (vt-seek f (the-vt) (the-vt-mask))
           ['()
            (DEBUG (eprintf "seek-check: no paths found for ~.s\n" (stx->datum f))
                   #;(eprintf "  the-vt = ~v\n" (the-vt))
                   #;(eprintf "  the-vt-mask = ~v\n" (the-vt-mask)))
            (k f v p s)]
           [(cons path more-paths)
            (DEBUG (eprintf "seek-check: found path ~s for ~.s within ~.s\n"
                            path (stx->datum f) (stx->datum v))
                   (let ([unique-paths (remove-duplicates (cons path more-paths))])
                     (when (> (length unique-paths) 1)
                       (eprintf "seek-check: multiple paths found for ~.s\n paths = ~v\n"
                                (stx->datum f) unique-paths))))
            (define vctx (path-replacer v path))
            ((parameterize ((the-context (cons vctx (the-context)))
                            (honesty 'T)
                            (the-vt #f)
                            (the-vt-mask null)
                            (marking-table (or (marking-table) (make-renames-mapping null null))))
               (RScase (k f f p s)
                       (lambda (f2 v2 p2 s2)
                         ;; inside parameterize
                         (define end-vt (the-vt))
                         (lambda ()
                           ;; outside parameterize
                           (the-vt (vt-merge-at-path (the-vt) path (or end-vt f2)))
                           ;; note: returning a true term into a fictional
                           ;; context does not increase honesty
                           (RSunit f2 (vctx v2) p s)))
                       (lambda (exn)
                         (lambda ()
                           (RSfail exn))))))])]))

;; ============================================================

;; A RenamesMapping is (renames-mapping Hasheq[Syntax => Stxish])
;; It represents a *forward* mapping from pre-rename to post-rename.

;; Note: for efficiency, we'll rely on the fact that pre and post contain no
;; artificial syntax. So to apply the renames mapping to a term that *contains*
;; the renamed parts, it's sufficient to recur through the term and *not* to
;; recur through syntax in pre. (This is not true for the macro hiding problem,
;; where a rename might contain the sought term; but that's a *backwards*
;; mapping problem.)

(struct renames-mapping (h) #:transparent
  #:property prop:procedure
  (lambda (self x) (hash-ref (renames-mapping-h self) x #f)))

(define (make-renames-mapping pre post)
  (define rm (renames-mapping (make-hash)))
  (begin (add-to-renames-mapping! rm pre post) rm))

(define (add-to-renames-mapping! rm from0 to0)
  (define table (renames-mapping-h rm))
  (define (stx-e x) (if (syntax? x) (syntax-e x) x))
  (let loop ([from from0] [to to0])
    ;; Some "renames" (sync) add structure---ie, map Stxish -> Syntax
    (cond [(or (syntax? from) (syntax? to))
           (hash-set! table from to)
           (loop (stx-e from) (stx-e to))]
          [(and (pair? from) (pair? to))
           (loop (car from) (car to))
           (loop (cdr from) (cdr to))]
          [(and (vector? from) (vector? to))
           (loop (vector->list from) (vector->list to))]
          [(and (box? from) (box? to))
           (loop (unbox from) (unbox to))]
          [(and (struct? from) (struct? to))
           (loop (struct->vector from) (struct->vector to))]
          [(eqv? from to)
           (void)]
          [else (void)])))

;; apply-renames-mapping : (Syntax -> Stx/#f) Stx -> Stx
(define (apply-renames-mapping rm stx #:resyntax? [resyntax? #f])
  (let loop ([stx stx])
    (cond [(rm stx) => values]
          [(syntax? stx)
           (let* ([inner (syntax-e stx)] ;; FIXME: disarm stx?
                  [rinner (loop inner)])
             (cond [(eq? rinner inner) stx]
                   [resyntax? (resyntax rinner stx)]
                   [else rinner]))]
          [(pair? stx)
           (let ([ra (loop (car stx))]
                 [rb (loop (cdr stx))])
             (cond [(and (eq? ra (car stx)) (eq? rb (cdr stx))) stx]
                   [else (cons ra rb)]))]
          [(vector? stx)
           (define relems (for/list ([e (in-vector stx)]) (loop e)))
           (cond [(for/and ([e (in-vector stx)] [re (in-list relems)]) (eq? e re))
                  stx]
                 [else (list->vector relems)])]
          [(box? stx)
           (let* ([inner (unbox stx)]
                  [rinner (loop inner)])
             (cond [(eq? rinner inner) stx]
                   [else (box inner)]))]
          [(prefab-struct-key stx)
           (let* ([inner (struct->vector stx)]
                  [rinner (loop inner)])
             (cond [(eq? rinner inner) stx]
                   [else (apply make-prefab-struct
                                (prefab-struct-key stx)
                                (cdr (vector->list rinner)))]))]
          [else stx])))

(define ((compose-renames-mappings rm1 rm2) x)
  (cond [(rm1 x) => rm2] [else #f]))

;; ============================================================
;; Marking table

(define marking-table (make-parameter #f)) ;; (Parameterof RenamesMapping/#f)

;; ============================================================

;; (Run reducer f v p s hole fill)
;; - let pctx be the context where hole occurs in p; need Pattern PVar -> Path / Paths fun
;; - let fctx be pctx wrt f; let vctx be pctx wrt v
;; - let init-e be the term s.t. f = fctx[init-e]
;; - let init-ev (vsub) be the term s.t. v = vctx[init-ev]
;; - recur on (reducer fill) with [init-e init-ev _ _] with context extended with ???

;; honesty never decreases on entry to context, only on hide, hidden step, and exit from context
;; honesty, not "visibility", determines visibility of most operations (FIXME: rename visibility)

(struct complete-fiction ())
(define the-fictional-term (complete-fiction))

;; run : (X -> RST) Stx Stx Pattern State Hole (U X (Listof X)) -> RS
;; where Hole = Symbol | (list Symbol '...) -- NOT a pattern value
;; Note: run restores pattern after running reducer
(define (run reducer f v p s hole fill)
  (match hole
    [(? symbol? hole)
     (define path (subpattern-path p hole))
     (run/path reducer f v p s path fill)]
    [(list (? symbol? hole) '...)
     (match-define (vector pre-path sub-path) (subpattern-path p hole #t))
     (let loop ([fill fill] [k 0] [f f] [v v] [s s])
       (match fill
         [(cons fill0 fill*)
          (define path (append pre-path (path-add-ref k sub-path)))
          (RSbind (run/path reducer f v p s path fill0)
                  (lambda (f v _p s) (loop fill* (add1 k) f v s)))]
         ['() (RSunit f v p s)]))]))

(define (run/path reducer f v p s path fill)
  (define fctx (path-replacer f path))
  (define sub-f (path-get f path))
  (define sub-hm (honesty-at-path (honesty) path))
  (DEBUG (eprintf "run/path: honesty ~s at path ~s => ~s\n" (honesty) path sub-hm))
  (define-values (vctx sub-v sub-vt sub-vt-mask)
    (cond [(eq? sub-hm 'F)
           ;; path might be out of bounds for v => can't take vctx => sub-v is meaningless
           ;; probably not much point in narrowing VT (and nontrivial to do right)
           ;; FIXME: it would be slightly better to know whether we were *inside* an F,
           ;;   because we care about whether the context is honest, not the term
           (define (identity-vctx x) x)
           (define sub-v v)
           (define sub-vt (the-vt))
           (define sub-vt-mask (the-vt-mask))
           (values identity-vctx sub-v sub-vt sub-vt-mask)]
          [else
           ;; can take vctx, but must also take narrowed VT (when sub-hm != 'T)
           (define vctx (path-replacer v path))
           (define sub-v (path-get v path))
           (define sub-vt (if (eq? sub-hm 'T) #f (the-vt)))
           (define sub-vt-mask (if sub-vt (append (the-vt-mask) path) null))
           (values vctx sub-v sub-vt sub-vt-mask)]))
  (DEBUG (eprintf "run/path: run ~s on f=~.s; v=~.s\n" reducer (stx->datum sub-f) (stx->datum sub-v)))
  ((parameterize ((the-context (cons vctx (the-context)))
                  (honesty sub-hm)
                  (the-vt sub-vt)
                  (the-vt-mask sub-vt-mask))
     (RScase ((reducer fill) sub-f sub-v (quote-pattern _) s)
             (lambda (f2 v2 _p2 _s2)
               ;; inside parameterize
               (define end-hm (honesty))
               (define end-vt (the-vt))
               (lambda ()
                 ;; outside of parameterize
                 (define merged-hm (honesty-merge-at-path (honesty) path end-hm))
                 (DEBUG
                  (eprintf "\n<< run/path merge old ~s and sub ~s => ~s\n"
                           (honesty) end-hm merged-hm)
                  (eprintf "  v => ~.s\n" (stx->datum (vctx v2))))
                 (honesty merged-hm)
                 (the-vt (cond
                           ;; Case: sub-hm < T, end-vt extends sub-vt
                           [sub-vt end-vt]
                           ;; Case: sub-hm = T but honesty decreased during subreduction
                           [end-vt
                            (if (the-vt)
                                (vt-merge-at-path (the-vt) (append (the-vt-mask) path) end-vt)
                                (vt-merge-at-path f path end-vt))]
                           ;; Case: sub-hm = end-hm = T
                           [else (the-vt)]))
                 (DEBUG
                  (eprintf "  vt => ~e\n" (the-vt))
                  (when (the-vt)
                    (eprintf "  vt-stx => ~.s\n" (stx->datum (vt->stx (the-vt) (the-vt-mask))))))
                 (RSunit (fctx f2 #:resyntax? #f) (vctx v2) p s)))
             (lambda (exn)
               (lambda () (RSfail exn)))))))

;; ------------------------------------

(provide check-same-stx)

(define (revappend a b)
  (cond [(pair? a) (revappend (cdr a) (cons (car a) b))]
        [(null? a) b]))

(define (check-same-stx function actual expected [derivs null])
  (unless (eq? actual expected)
    (let* ([actual-datum (stx->datum actual)]
           [expected-datum (stx->datum expected)]
           [same-form? (equal? actual-datum expected-datum)])
      (if same-form?
          (eprintf "same form but wrong wrappings:\n~.s\nwrongness:\n~.s\n"
                   actual-datum
                   (wrongness actual expected))
          (eprintf "got:\n~.s\n\nexpected:\n~.s\n"
                   actual-datum
                   expected-datum))
      (for ([d derivs]) (eprintf "\n~.s\n" d))
      (error function
             (if same-form?
                 "wrong starting point (wraps)!"
                 "wrong starting point (form)!")))))

(define (stx-eq-diff a b)
  (let loop ([a a] [b b])
    (cond [(and (stx-null? a) (stx-null? b)) '()]
          [(equal? a b) '_]
          [(stx-pair? a)
           (cons (loop (stx-car a) (stx-car b))
                 (loop (stx-cdr a) (stx-cdr b)))]
          [else
           (unless (equal? (stx->datum a) (stx->datum b))
             (error 'stx-eq-diff "different shapes: ~.s, ~.s" a b))
           (stx->datum a)])))

(define (wrongness a b)
  (cond [(eq? a b)
         '---]
        [(stx-list? a)
         (map wrongness (stx->list a) (stx->list b))]
        [(stx-pair? a)
         (cons (wrongness (stx-car a) (stx-car b))
               (wrongness (stx-cdr a) (stx-cdr b)))]
        [else (stx->datum a)]))

;; flatten-identifiers : syntaxlike -> (list-of identifier)
(define (flatten-identifiers stx)
  (syntax-case stx ()
    [id (identifier? #'id) (list #'id)]
    [() null]
    [(x . y) (append (flatten-identifiers #'x) (flatten-identifiers #'y))]
    [else (error 'flatten-identifiers "neither syntax list nor identifier: ~s"
                 (if (syntax? stx)
                     (syntax->datum stx)
                     stx))]))

;; ============================================================
;; Macro hiding

;; There are two aspects of the state of the reductions generator:

;; - visibility: Are we showing or hiding steps on the current *actual* local
;;   term? This is controlled by the hiding policy.

;; - honesty: Does the current *visible* local term correspond to the current
;;   *actual* local term? This depends on the history of visibility within the
;;   current context and the (partly) on the honesty of the parent context.

;; There are three modes (combinations of visibility and honesty):

;; - truth   = visible and honest
;; - gossip  = visible and not honest
;; - fiction = not visible and not honest

;; The mode (not visible but honest) exists only briefly on entry to macro
;; hiding; it is reasonable to merge it with (not visible and not honest).

;; The mode has the following consequences:
;; - on *steps*
;;   - truth: the step can be shown, and it updates the visible term
;;   - gossip: the step cannot be shown, or it must be simulated
;;     Consider the actual expansion (#%expression A) -> (#%expression A*) -> A*.
;;     If hiding produces (#%expression A) -> (#%expression A**), then we cannot
;;     apply the step (#%expression A*) -> A*. There are two options:
;;     - drop the step
;;     - simulation: rewrite the step to (#%expression A**) -> A**; this
;;       requires custom code for each step (?)
;;   - fiction: the step is not shown, and the visible term is not updated
;;     (FIXME: need to separate rewrite from tracking in such steps, apply tracking!)
;; - on entering a new context for reduction:
;;   - truth: the mode of the new context is still truth
;;   - gossip: if we know the context refers to a true subterm of the visible
;;     term, we can enter truth mode (see Honesty Masks); otherwise we must stay
;;     in gossip mode
;;   - fiction: the mode of the new context is still fiction
;; - on returning from a context:
;;   - truth: the parent context's mode is unchanged
;;   - gossip/fiction: the parent context's mode changes:
;;     - parent mode was truth or gossip -> becomes gossip
;;     - parent mode was fiction -> stays fiction

;; Once we enter gossip (or fiction) mode, the visible term is not Stx, but a
;; special data structure for tracking visible subterms. See Tracking.

;; Why not unify gossip and fiction modes?
;; - PRO: They're nearly the same in practice, which argues for unifying.
;; - CON: Consider (λ () (define x A) (begin 1 2)), and suppose define is hidden.
;;   In gossip mode with honesty mask, we have a hope of showing begin splicing.
;; - CON: In (#%app e1 ... ek), we create known independent contexts for subexprs.
;;   Fiction in e1 should not affect e2. But maybe this is just a special case of
;;   (HOLE ...) contexts?

;; ----------------------------------------
;; Tracking

;; Forward mode: representation of visible term is Stx. Adjustments
;; are applied as they occur.

;; Backward mode: representation is VT; see tracking.rkt.

;; ----------------------------------------
;; Honesty Masks

;; An *honesty mask* indicates what parts of the current term may be fictional.

;; An HonestyMask is one of
;; - 'F -- (partly, potentially) fictional term
;; - 'T -- true term
;; - (cons HonestyMask HonestyMask) -- a true pair

;; Note: Since HonestyMask < Stxish, can use path functions on HonestyMasks.

;; hmcons : HonestyMask HonestyMask -> HonestyMask
;; Note: (cons T T) = T --- pair might be artificial, but can sync? (FIXME)
(define (hmcons hm1 hm2) (if (and (eq? hm1 'T) (eq? hm2 'T)) 'T (cons hm1 hm2)))

;; honesty-at-path : HonestyMask Path -> HonestyMask
(define (honesty-at-path hm path)
  (define-values (hm* path*) (path-get-until hm path symbol?))
  ;; Either we used whole path, or we stopped short at 'T or 'F, and
  ;; the subterms of a 'T or 'F term is 'T or 'F, respectively.
  hm*)

;; honesty-merge : HonestyMask HonestyMask -> HonestyMask
(define (honesty-merge hm1 hm2)
  (let loop ([hm1 hm1] [hm2 hm2])
    (match* [hm1 hm2]
      [['T hm] hm]
      [[hm 'T] hm]
      [[(cons hm1a hm1b) (cons hm2a hm2b)]
       (hmcons (loop hm1a hm2a) (loop hm1b hm2b))]
      [[_ _] 'F])))

;; honesty-merge-at-path: HonestyMask Path HonestyMask -> HonestyMask
;; Merges the first hm's subtree at path with second subtree.
(define (honesty-merge-at-path hm1 path hm2)
  (define (loop hm1 path)
    (match path
      ['() (honesty-merge hm1 hm2)]
      [(cons 'car path)
       (match hm1
         [(cons hm1a hm1b) (cons (loop hm1a path) hm1b)]
         ['T (hmcons (loop 'T path) 'T)]
         ['F 'F])]
      [(cons (? exact-positive-integer? n) path)
       (let tailloop ([hm1 hm1] [n n])
         (cond [(zero? n) (loop hm1 path)]
               [else
                (match hm1
                  [(cons hm1a hm1b) (hmcons hm1a (tailloop hm1b (sub1 n)))]
                  ['T (hmcons 'T (tailloop 'T (sub1 n)))]
                  ['F 'F])]))]))
  (loop hm1 path))

;; An HonestyMaskSpec extends HonestyMask with
;; - #(hmrep HonestyMask) -- a true list whose elements have the given honesty
(struct hmrep (hm) #:prefab)

;; honesty>=? : HonestyMask HonestyMaskSpec -> Boolean
;; Retuns #t if hm1 is at least as honest as hm2.
(define (honesty>=? hm1 hm2)
  (let loop ([hm1 hm1] [hm2 hm2])
    (match* [hm1 hm2]
      [['T _] #t]
      [[_ 'F] #t]
      [[(cons hm1a hm1b) (cons hm2a hm2b)]
       (and (loop hm1a hm2a) (loop hm1b hm2b))]
      [[(cons hm1a hm1b) (hmrep hm2e)]
       (and (loop hm1a hm2e) (loop hm1b hm2))]
      [[_ _] #f])))
