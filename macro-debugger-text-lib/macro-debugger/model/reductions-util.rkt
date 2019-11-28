#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         racket/stxparam
         racket/contract/base
         racket/list
         syntax/stx
         racket/match
         "deriv-util.rkt"
         "stx-util.rkt"
         "pattern.rkt"
         "context.rkt"
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

;; FIXME: change ws (reduction sequence) from threaded to synthesized (jumble, flatten at end?)
;; ;; A (Jumbleof X) is anything that flattens to a (Listof X) -- X must not be pair or null
;; (define (jcons a b) (cond [(null? a) b] [(null? b) a] [else (cons a b)]))
;; (define (jumble->list j) (flatten j))

;; ============================================================
;; Expansion Context

(provide
 (contract-out
  [the-phase (parameter/c exact-nonnegative-integer?)]
  [the-context (parameter/c list?)]
  [the-big-context (parameter/c (listof bigframe?))])
 with-context
 with-new-local-context)

(define the-phase (make-parameter 0))
(define the-context (make-parameter null))
(define the-big-context (make-parameter null))

;; syntax (with-context Expr[Frame] body ...+)
(define-syntax-rule (with-context f . body)
  (parameterize ((the-context (cons f (the-context)))) . body))

;; syntax (with-new-local-context Expr[???] body ...+)
(define-syntax-rule (with-new-local-context e . body)
  (let ([x e])
    (parameterize ((the-big-context (cons (bigframe (the-context) (list x) x) (the-big-context)))
                   (the-context null))
      (let () . body))))

;; ============================================================
;; Expansion State

(provide
 (struct-out xstate)
 (contract-out
  [the-xstate (parameter/c (or/c xstate? #f))]
  [new-xstate (-> xstate?)]
  [next-seqno (-> exact-nonnegative-integer?)])
 ;; FIXME
 learn-binders 
 learn-definites
 add-lift
 add-endlift
 get/clear-lifts
 get/clear-endlifts
 add-frontier
 clear-frontier)

;; An XState is:
(struct xstate
  (seqno        ;; Nat
   binders      ;; ImmutableHasheq[Identifier => Phase]
   definites    ;; ImmutableHasheq[Identifier => Phase]
   lifts        ;; (Listof Lift)
   endlifts     ;; (Listof Syntax)
   frontier     ;; ImmutableHashEq[Syntax => #t]
   ) #:transparent #:mutable)
;; where Lift = (list 'def Ids Syntax) | (list 'req Syntax) | (list 'mod Syntax)

;; the-xstate : (Parameterof XState/#f)
(define the-xstate (make-parameter #f))

;; new-xstate : -> XState
(define (new-xstate)
  (xstate 0 '#hasheq() '#hasheq() null null '#hasheq()))

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

;; add-frontier : (Listof Syntax) -> Void
;; clear-frontier : (Listof Syntax) -> Void
(define (add-frontier stxs #:xstate [xst (the-xstate)])
  (set-xstate-frontier! xst (hash-set-list (xstate-frontier xst) (flatten stxs) #t)))
(define (clear-frontier stxs #:xstate [xst (the-xstate)])
  (set-xstate-frontier! xst (hash-remove-list (xstate-frontier xst) (flatten stxs))))


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
  #;
  (eprintf "current-state-with: ~e, ~e; ~e\n" (stx->datum e) (stx->datum fs)
           (stx->datum (for/fold ([x 'HOLE]) ([p (the-context)]) (p x))))
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
   (-> syntaxish? syntaxish? pattern/c state/c reduction-sequence/c RS/c)]
  [RSfail
   (-> reduction-sequence/c exn? RS/c)]
  [RSbind
   (-> RS/c (-> any/c any/c state/c reduction-sequence/c RS/c) RS/c)]
  [RScase
   (-> RS/c
       (-> any/c any/c any/c state/c reduction-sequence/c any)
       (-> exn? reduction-sequence/c any)
       any)]
  [RSreset
   (->* [RS/c] [#:pattern (or/c pattern/c #f)] RS/c)]))

;; RS = (rsok ReductionSequence Stx Stx State)
;;    | (rsfailed ReductionSequence Exn)
(struct rsok (f v p s ws))
(struct rsfailed (exn ws))

(define RS/c (or/c rsok? rsfailed?))

(define pattern/c any/c) ;; FIXME?

(define RST/c
  ;; First two args are any/c instead of syntaxish? because of
  ;; #:new-local-context that initially sets syntax to #f.
  (-> (or/c syntaxish? #f) (or/c syntaxish? #f) pattern/c state/c reduction-sequence/c
      RS/c))

(define (RSunit f v p s ws) (rsok f v p s ws))
(define (RSfail exn ws) (rsfailed exn ws))

(define (RSbind a fun)
  (match a
    [(rsok f v p s ws) (fun f v p s ws)]
    [(rsfailed exn rs) a]))

(define (RScase a ok fail)
  (match a
    [(rsok f v p s ws) (ok f v p s ws)]
    [(rsfailed exn rs) (fail exn rs)]))

(define (RSreset a #:pattern [reset-p #f])
  (RSbind a (lambda (f v p s ws) (RSunit f v (or reset-p p) s ws))))


;; ============================================================
;; Implicit match from #:pattern

(provide % %e)

(define-syntax-parameter the-match-result
  (lambda (stx)
    (raise-syntax-error #f "no match result; used outside of wrap-user-expr" stx)))

(define-syntax-rule (% p) (%e (quote-template-pattern p)))
(define-syntax-rule (%e p) (pattern-template p the-match-result))

(define-syntax wrap-user-expr
  (syntax-parser
    [(_ [f v p] expr:expr)
     #'(let ([mv (pattern-match p f)])
         #;(eprintf "wrap-user-expr: pattern match ~s, ~e = ~e\n" p f mv)
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
          '#:left-foot #'R/left-foot
          '#:step #'R/step
          '#:walk #'R/walk
          '#:rename #'R/rename
          '#:rename/mark #'R/rename/mark
          '#:rename/unmark #'R/rename/unmark
          '#:new-local-context #'R/new-local-context
          '#:reductions #'R/reductions
          '#:if #'R/if
          '#:when #'R/when
          '#:pass1 #'R/pass1
          '#:pass2 #'R/pass2
          '#:in-hole #'R/in-hole
          #|
          '#:hide-check #'R/hide-check
          '#:seek-check #'R/seek-check
          |#))

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
  (lambda (f v p s ws) (R** f v p s ws . clauses)))

;; syntax (R** f v p s ws RClause ...) : RS
(define-syntax R**
  (syntax-parser
    #:literals (=>)
    [(R** f v p s ws)
     #'(RSunit f v p s ws)]
    [(R** f v p s ws => k . more)
     #:declare k (expr/c #'RST/c)
     #'(RSbind (RSreset (k.c f v p s ws) #:pattern p)
               (R . more))]
    [(R** f v p s ws c:RClause . more)
     #'(begin
         #;
         (let ([cstx (quote-syntax c)])
           (eprintf "doing [~s:~s] ~e\n" (syntax-line cstx) (syntax-column cstx) (quote c)))
         (c.macro f v p s ws c (R . more)))]))

;; A R/<Clause> macro has the form
;;   (R/<Clause> f v p s ws <Clause> kexpr)
;; where f,v,p,w,ws are *variables* and kexpr is *expression*
;; - f is the "real" form
;; - v is the "virtual/visible" form (used for steps)
;; - p is the current pattern
;; - s is the last marked state, or #f
;; - ws is the list of steps, reversed
;; - kexpr is the continuation (RST)

(define-syntax R/!
  (syntax-parser
    #:literals (!)
    ;; Error-point case
    [(_ f v p s ws [! maybe-exn] ke)
     #:declare maybe-exn (expr/c #'(or/c exn? #f))
     #'(let ([x maybe-exn.c])
         (if x
             (RSfail x (cons (stumble v x) ws))
             (ke f v p s ws)))]))

(define-syntax R/pattern
  (syntax-parser
    ;; Change patterns
    [(_ f v p s ws [#:pattern p2] ke)
     #'(ke f v (quote-pattern p2) s ws)]))

(define-syntax R/do
  (syntax-parser
    ;; Execute expressions for effect
    [(_ f v p s ws [#:do expr ...] ke)
     #'(begin
         (wrap-user-expr [f v p] (let () expr ... (void)))
         (ke f v p s ws))]))

(define-syntax R/let
  (syntax-parser
    [(_ f v p s ws [#:let var:id expr] ke)
     #'(let ([var (wrap-user-expr [f v p] expr)])
         (ke f v p s ws))]))

(define-syntax R/parameterize
  (syntax-parser
    [(_ f v p s ws [#:parameterize ((param expr) ...) . clauses] ke)
     #:declare param (expr/c #'parameter?)
     #'(RSbind (parameterize ((param.c (wrap-user-expr [f v p] expr)) ...)
                 (R** f v p s ws . clauses))
               ke)]))

;; FIXME: WHEN?
(define-syntax R/set-syntax
  (syntax-parser
    ;; Change syntax
    [(_ f v p s ws [#:set-syntax form] ke)
     #:declare form (expr/c #'syntaxish?)
     #'(let ([f2 (wrap-user-expr [f v p] form.c)])
         (ke f2 f2 p s ws))]))

(define-syntax R/left-foot
  (syntax-parser
    [(_ f v p s ws [#:left-foot (~optional fs)] ke)
     #:declare fs (expr/c #'syntaxish?)
     #'(let ([s2 (current-state-with v (~? (wrap-user-expr [f v p] fs.c) v))])
         (ke f v p s2 ws))]))

(define-syntax R/step
  (syntax-parser
    [(_ f v p s ws [#:step type (~optional fs)] ke)
     #:declare fs (expr/c #'syntaxish?)
     #:declare type (expr/c #'(or/c step-type? #f))
     #'(let ()
         (define s2 (current-state-with v (~? (wrap-user-expr [f v p] fs.c) v)))
         (define type-var type.c)
         (define ws2 (if type-var (cons (make step type-var s s2) ws) ws))
         (ke f v p s2 ws2))]))

(begin-for-syntax
  (define-syntax-class walk-clause
    #:attributes (form1.c form2.c foci1.c foci2.c type)
    (pattern [#:walk form2 type:expr
              (~alt (~optional (~seq #:foci foci2))
                    (~optional (~seq #:from form1))
                    (~optional (~seq #:from-foci foci1))) ...]
             #:declare form1 (expr/c #'syntaxish?)
             #:declare foci1 (expr/c #'syntaxish?)
             #:declare form2 (expr/c #'syntaxish?)
             #:declare foci2 (expr/c #'syntaxish?))))

(define-syntax R/walk
  (syntax-parser
    [(_ f v p s ws w:walk-clause ke)
     #'(let ()
         (define-values (f1 fs1 f2 fs2 type)
           (wrap-user-expr [f v p]
                           (let ([f2 w.form2.c])
                             (values (~? w.form1.c v)
                                     (~? w.foci1.c v)
                                     f2
                                     (~? w.foci2.c f2)
                                     w.type))))
         (define s1 (current-state-with f1 fs1))
         (define s2 (current-state-with f2 fs2))
         (define ws2 (if type (cons (make step type s1 s2) ws) ws))
         (ke f2 f2 p s2 ws2))]))

;; STOPPED HERE





(define-syntax R/reductions
  (syntax-parser
    [(_ f v p s ws [#:reductions rs] ke)
     #:declare rs (expr/c #'reduction-sequence/c)
     #'(let ([ws2 (revappend (wrap-user-expr [f v p] rs.c) ws)])
         (ke f v p s ws2))]))

(define-syntax R/rename
  (syntax-parser
    ;; Rename
    [(_ f v p s ws [#:rename pattern renames] ke)
     #'(R/rename f v p s ws [#:rename pattern renames #f] ke)]
    [(_ f v p s ws [#:rename pattern renames description] ke)
     #'(R/rename* f v p s ws [#:rename* pattern renames description #f] ke)]))

(define-syntax R/rename*
  (syntax-parser
    [(_ f v p s ws [#:rename* pattern renames description mark-flag] ke)
     #'(RSbind (let ()
                 (define pattern-var (quote-pattern pattern))
                 (define-values (renames-var description-var mark-flag-var)
                   (wrap-user-expr [f v p] (values renames description mark-flag)))
                 (do-rename f v p s ws pattern-var renames-var description-var mark-flag-var))
               ke)]))

(define (do-rename f v p s ws ren-p renames description mark-flag)
  (define pre-renames (pattern-template ren-p (pattern-match p f)))
  (define f2 (pattern-replace p f ren-p renames))
  #;(eprintf "do-rename: ~s => ~s\n" (stx->datum f) (stx->datum f2))
  (define whole-form-rename? (equal? p ren-p)) ;; FIXME is this right?
  (define renames-mapping (make-renames-mapping pre-renames renames))
  (define v2 (apply-renames-mapping renames-mapping v))
  (define ws2 
    (if description
        (cons (walk v v2 description #:foci1 pre-renames #:foci2 renames) ws)
        ws))
  (RSunit f2 v2 p s ws2))

(define-syntax R/rename/mark
  (syntax-parser
    [(_ f v p s ws [#:rename/mark pvar from to] ke)
     #:declare from (expr/c #'syntaxish?)
     #:declare to (expr/c #'syntaxish?)
     #'(let ([real-from (wrap-user-expr [f v p] (% pvar))])
         (R/rename* f v p s ws [#:rename* pvar to #f 'mark] ke))]))

(define-syntax R/rename/unmark
  (syntax-parser
    [(_ f v p s ws [#:rename/unmark pvar from to] ke)
     #:declare from (expr/c #'syntaxish?)
     #:declare to (expr/c #'syntaxish?)
     #'(let ([real-from (wrap-user-expr [f v p] (% pvar))])
         (R/rename* f v p s ws [#:rename* pvar to #f 'unmark] ke))]))

(define-syntax R/if
  (syntax-parser
    ;; Conditional (pattern changes lost afterwards ...) ;; FIXME???
    [(_ f v p s ws [#:if test [consequent ...] [alternate ...]] ke)
     #'(RSbind (RSreset (if (wrap-user-expr [f v p] test)
                            (R** f v p s ws consequent ...)
                            (R** f v p s ws alternate ...))
                        #:pattern p)
               ke)]))

(define-syntax R/when
  (syntax-parser
    ;; Conditional (pattern changes lost afterwards ...) ;; FIXME???
    [(_ f v p s ws [#:when test consequent ...] ke)
     #'(R/if f v p s ws [#:if test [consequent ...] []] ke)]))


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
    [(_ f v p s ws [#:pass1] ke)
     #'(ke f v p s ws)]))

(define-syntax R/pass2
  (syntax-parser
    [(_ f v p s ws [#:pass2 clause ...] ke)
     #'(ke f v p s ws)]))

(define-syntax R/new-local-context
  (syntax-parser
    [(_ f v p s ws [#:new-local-context clause ...] ke)
     #'(let ([process-clauses (lambda () (R** #f #f '_ #f ws clause ...))])
         (RSbind (with-new-local-context v (process-clauses))
                 (lambda (f2 v2 _p s2 ws2)
                   (let ([v2 v] [s2 s])
                     (ke f v2 p s2 ws2)))))]))

(define-syntax R/run
  (syntax-parser
    ;; Subterm handling
    [(R** f v p s ws [reducer hole fill] ke)
     #:declare reducer (expr/c #'(-> any/c RST/c))
     #'(RSbind (run reducer.c f v p s ws (quote hole) fill)
               ke)]))

;; FIXME: should this be used more?
(define-syntax R/in-hole
  (syntax-parser
    [(_ f v p s ws [#:in-hole hole . clauses] ke)
     #'(RSbind (let ([reducer (lambda (_) (R . clauses))])
                 (run reducer f v p s ws (quote hole) #f))
               ke)]))

;; ============================================================

;; A RenamesMapping is (renames-mapping Stxish Stxish Hasheq[Syntax => Stxish])
;; It represents a *forward* mapping from pre-rename to post-rename.

;; Note: for efficiency, we'll rely on the fact that pre and post contain no
;; artificial syntax. So to apply the renames mapping to a term that *contains*
;; the renamed parts, it's sufficient to recur through the term and *not* to
;; recur through syntax in pre. (This is not true for the macro hiding problem,
;; where a rename might contain the sought term; but that's a *backwards*
;; mapping problem.)

(struct renames-mapping (pre post h) #:transparent)

(define (make-renames-mapping pre post)
  (renames-mapping pre post
                   (let loop ([pre pre] [post post] [h '#hasheq()])
                     (cond [(pair? pre)
                            (loop (car pre) (stx-car post)
                                  (loop (cdr pre) (stx-cdr post) h))]
                           [(syntax? pre)
                            (hash-set h pre post)]
                           [else h]))))


(define (apply-renames-mapping renmap v)
  (define h (renames-mapping-h renmap))
  (let loop ([v v])
    (cond [(syntax? v)
           (or (hash-ref h v #f)
               (cond [(syntax-unarmed? v)
                      (define r (loop (syntax-e v)))
                      (cond [(eq? r (syntax-e v)) v]
                            [else (resyntax r v v)])]
                     [else v]))]
          [(pair? v)
           (define r1 (loop (car v)))
           (define r2 (loop (cdr v)))
           (cond [(and (eq? r1 (car v)) (eq? r2 (cdr v))) v]
                 [else (cons r1 r2)])]
          [else v])))

;; ============================================================

;; (Run reducer f v p s ws hole fill)
;; - let pctx be the context where hole occurs in p; need Pattern PVar -> Path / Paths fun
;; - let fctx be pctx wrt f; let vctx be pctx wrt v
;; - let init-e be the term s.t. f = fctx[init-e]
;; - let init-ev (vsub) be the term s.t. v = vctx[init-ev]
;; - recur on (reducer fill) with [init-e init-ev _ _ ws] with context extended with ???

;; run : (X -> RST) Stx Stx Pattern State ReductionSequence Hole (U X (Listof X)) -> RS
;; where Hole = Symbol | (list Symbol '...) -- NOT a pattern value
;; Note: run restores pattern after running reducer
(define (run reducer f v p s ws hole fill)
  (match hole
    [(? symbol? hole)
     (define path (subpattern-path p hole))
     #;(eprintf "run: found ~s in ~s at ~s\n" hole p path)
     (define fctx (path-replacer f path))
     (define vctx (path-replacer v path))
     (define init-sub-f (path-get f path))
     (define init-sub-v (path-get v path))
     (run-one reducer init-sub-f fctx init-sub-v vctx fill p s ws)]
    [(list (? symbol? hole) '...)
     (match-define (vector pre-path sub-path) (subpattern-path p hole #t))
     #;(eprintf "run (multi) paths: ~e, ~e" pre-path sub-path)
     (let loop ([fill fill] [k 0] [f f] [v v] [s s] [ws ws])
       #;(eprintf "run (multi): k = ~s, fill length = ~s\n" k (length fill))
       (match fill
         [(cons fill0 fill*)
          (define path (append pre-path (path-add-ref k sub-path)))
          (define fctx (path-replacer f path))
          (define vctx (path-replacer v path))
          (define init-sub-f (path-get f path))
          (define init-sub-v (path-get v path))
          (RSbind (run-one reducer init-sub-f fctx init-sub-v vctx fill0 p s ws)
                  (lambda (f v _p s ws) (loop fill* (add1 k) f v s ws)))]
         ['() (RSunit f v p s ws)]))]))

;; run-one : (X -> RST) Stx (Stx -> Stx) Stx (Stx -> Stx) X Pattern State RedSeq -> RS
(define (run-one reducer init-f fctx init-v vctx fill p s ws)
  (RSbind (with-context vctx
            #;
            (eprintf "run-one: ~s on ~s in ~s --- ~s\n" reducer (stx->datum init-v)
                     (stx->datum (vctx 'HOLE))
                     (stx->datum (for/fold ([x 'HOLE]) ([p (the-context)]) (p x))))
            ((reducer fill) init-f init-v (quote-pattern _) s ws))
          (lambda (f2 v2 _p s2 ws2)
            (RSunit (fctx f2 #:resyntax? #f) (vctx v2) p s2 ws2))))

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

;; ----------------------------------------
;; Honesty Masks

#|

(define visible? (make-parameter #t))
(define honest? (make-parameter #t))

;; We can more precisely quantify honesty with an *honesty mask*: a tree that
;; indicates what parts of the current term may be fictional.

;; An HonestyMask is one of
;; - 'F -- (partly, potentially) fictional term
;; - 'T -- true term
;; - (cons HonestyMask HonestyMask) -- a true pair with descriptions of its components' honesty
;; * #(hmrep HonestyMask) -- a true list whose elements have the given honesty (only in specs?)
(struct hmrep (hm) #:prefab)

;; honesty>=? : HonestyMask HonestyMask -> Boolean
;; Retuns #t if hm1 is at least as honest as hm2.
(define (honesty>=? hm1 hm2)
  ...)

(define (honest? [hm (honesty-mask)])
  (honesty>=? hm 'T))

|#
