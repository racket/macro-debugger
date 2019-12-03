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
  (when #f form ... (void)))

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
(define honesty (make-parameter 'T))        ;; (Parameterof HonestyMask)

(define (call-with-initial-context proc #:xstate xst)
  (parameterize ((the-xstate xst)
                 (the-phase 0)
                 (the-context null)
                 (the-big-context null)
                 (the-vt #f)
                 (honesty 'T))
    (proc)))

;; set-honesty : HonestyMask Stx -> Void
;; PRE: hm <= (honesty) -- that is, honesty is only decreased or left unchanged
;; Invariant: (honesty) = 'T  iff  (the-vt) = #f
(define (set-honesty hm f)
  (define current-hm (honesty))
  (DEBUG (unless (eq? (honesty) hm) (eprintf "set-honesty : ~s => ~s\n" (honesty) hm)))
  (unless (equal? current-hm hm)
    (when (eq? current-hm 'T) (the-vt (vt-base f)))
    (honesty hm)))

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
;; RS: the reduction monad

;; This monad acts like an Exception monad whose success type is always
;; specialized to a 4-tuple containing the *local* reduction state: real term,
;; visible term, pattern, and state (cf step.rkt).

;; Contextual state and threaded state are handled by parameters and a
;; parameter-held "xstate" mutable object (see later sections).

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

;; In a subexpression of an R-clause (see below), the % and %e macros have
;; access to the pattern variables bound by matching the current term (f)
;; against the current pattern (p).

;; Unlike with-syntax and #', pattern-match and % never create syntax
;; objects. Also, patterns here are first-class values, which simplifies
;; continuation management.

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
;; The Reduction Language

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
         (DEBUG (do-debug-clause (quote c) (quote-syntax c) v))
         (c.macro f v p s c (R . more)))]))

(define (do-debug-clause c cstx v)
  (define where (format "[~s:~s]" (syntax-line cstx) (syntax-column cstx)))
  (eprintf "doing ~a ~.s, honesty = ~s, v = ~.s\n"
           where (trim-quoted-clause c) (honesty) (stx->datum v)))

(define (trim-quoted-clause c)
  (define (abbrev-kw? x) (memq x '(#:parameterize #:when #:if #:with-marking #:do)))
  (match c [(cons (? abbrev-kw? kw) _) `(,kw _)] [_ c]))

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
             (do-rename-v v (the-vt) (honesty) pre-renames renames))
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

(define (do-rename-v v vt hm pre post)
  (DEBUG
   (eprintf " do-rename-v, vt depth = ~s\n" (vt-depth vt))
   (eprintf "  vt-stx = ~.s\n" (stx->datum (vt->stx vt))))
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
             (match (vt-seek pre vt)
               [(cons path _)
                (DEBUG
                 (eprintf "  found at ~s, pre = ~.s\n" path (stx->datum pre))
                 (with-handlers ([exn?
                                  (lambda (e)
                                    (eprintf "** vt = \n")
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
(define-syntax-rule (R/with-marking f v p s [#:with-marking c ...] ke)
  (RSbind ((R c ...) f v p s) ke))

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
    ;; FIXME: set-honesty needs to rebuild table if honesty strictly *decreases*
    (set-honesty 'F f))
  (k f v p s))

(define-syntax-rule (R/seek-check f v p s [#:seek-check] ke)
  (do-seek-check f v p s ke))

(define (do-seek-check f v p s k)
  (cond [(honest?) (k f v p s)]
        [else
         (match (vt-seek f (the-vt))
           ['()
            (DEBUG (eprintf "seek-check: no paths found for ~.s\n" (stx->datum f))
                   #;(eprintf "  the-vt = ~v\n" (the-vt)))
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
                            (the-vt #f))
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
  (define-values (vctx sub-v sub-vt)
    (cond [(eq? sub-hm 'F)
           ;; path might be out of bounds for v => can't take vctx => sub-v is meaningless
           ;; probably not much point in narrowing VT (and nontrivial to do right)
           ;; FIXME: it would be slightly better to know whether we were *inside* an F,
           ;;   because we care about whether the context is honest, not the term
           (define (identity-vctx x) x)
           (define sub-v v)
           (define sub-vt (the-vt))
           (values identity-vctx sub-v sub-vt)]
          [else
           ;; can take vctx, but must also take narrowed VT (when sub-hm != 'T)
           (define vctx (path-replacer v path))
           (define sub-v (path-get v path))
           (define sub-vt (if (eq? sub-hm 'T) #f (vt-zoom (the-vt) path)))
           (values vctx sub-v sub-vt)]))
  (DEBUG (eprintf "run/path: run ~s on f=~.s; v=~.s\n" reducer (stx->datum sub-f) (stx->datum sub-v)))
  ((parameterize ((the-context (cons vctx (the-context)))
                  (honesty sub-hm)
                  (the-vt sub-vt))
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
                           ;; Case: sub-hm = F
                           ;; - then sub-vt was not zoomed, end-vt extends sub-vt, return as is
                           [(eq? sub-hm 'F) end-vt]
                           ;; Case: sub-hm > F and sub-vt != #f
                           ;; - then sub-vt was zoomed, end-vt extends it, so unzoom end-vt
                           [sub-vt (vt-unzoom end-vt path)]
                           ;; Case: sub-hm = T and end-vt != #f -- honesty decreased during reducer
                           [end-vt
                            (if (the-vt)
                                (vt-merge-at-path (the-vt) path end-vt)
                                (vt-merge-at-path f path end-vt))]
                           ;; Case: sub-hm = end-hm = T
                           [else (the-vt)]))
                 (DEBUG
                  (eprintf "  vt => ~e\n" (the-vt))
                  (when (the-vt)
                    (eprintf "  vt-stx => ~.s\n" (stx->datum (vt->stx (the-vt))))))
                 (RSunit (fctx f2 #:resyntax? #f) (vctx v2) p s)))
             (lambda (exn)
               (lambda () (RSfail exn)))))))

;; ------------------------------------

(define (revappend a b)
  (cond [(pair? a) (revappend (cdr a) (cons (car a) b))]
        [(null? a) b]))

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
