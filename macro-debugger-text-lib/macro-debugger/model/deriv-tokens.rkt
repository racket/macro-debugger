#lang racket/base
(require parser-tools/lex
         "deriv.rkt")
(provide (all-defined-out))

;; NOTE: trace.rkt also depends on some token numbers
;; eg for enter-macro, local-value, etc

(define-tokens basic-empty-tokens
  (start                ; .
   start-top            ; .
   start-ecte           ; .
   next                 ; .
   next-group           ; .
   phase-up             ; .
   ...                  ; .
   EOF                  ; .
   enter-bind           ; .
   exit-bind            ; .
   exit-local-bind      ; .
   IMPOSSIBLE           ; useful for error-handling clauses that have no
                        ; NoError counterpart
   top-non-begin        ; .
   prepare-env          ; .
   ))

(define-tokens basic-tokens
  (visit                ; syntax
   resolve              ; identifier
   enter-macro          ; syntax
   macro-pre-x          ; syntax
   macro-post-x         ; (cons syntax syntax)
   exit-macro           ; syntax
   enter-prim           ; syntax
   exit-prim            ; syntax
   return               ; syntax
   enter-block          ; syntaxes
   block->list          ; syntaxes
   block->letrec        ; syntax(es?)
   splice               ; syntaxes
   enter-list           ; syntaxes
   exit-list            ; syntaxes
   enter-check          ; syntax
   exit-check           ; syntax
   module-body          ; (list-of (cons syntax boolean))
   syntax-error         ; exn
   lift-loop            ; syntax = new form (let or begin; let if for_stx)
   letlift-loop         ; syntax = new let form
   module-lift-loop     ; syntaxes = def-lifts, in reverse order lifted (???)
   module-lift-end-loop ; syntaxes = statement-lifts ++ provide-lifts, in order lifted
   lift-expr            ; (cons (listof id) syntax)
   lift-statement       ; syntax
   lift-require         ; (cons syntax (cons syntax syntax))
   lift-provide         ; syntax

   enter-local          ; syntax
   local-pre            ; syntax
   local-post           ; syntax
   exit-local           ; syntax

   local-bind           ; (listof identifier)
   opaque-expr          ; opaque-syntax

   variable             ; (cons identifier identifier)
   tag                  ; syntax

   rename-one           ; syntax
   rename-list          ; (list-of syntax)
   lambda-renames       ; (cons syntax syntax)
   let-renames          ; (cons (listof syntax) syntax)
   letrec-syntaxes-renames ; (cons (listof syntax) (cons (listof syntax) syntax))
   block-renames        ; (cons syntax syntax) ... contains both pre+post

   top-begin            ; identifier

   local-remark         ; (listof (U string syntax))
   local-artificial-step ; (list syntax syntax syntax syntax)

   track-origin         ; (cons stx stx)
   local-value          ; identifier
   local-value-result   ; boolean
   local-value-binding  ; result of identifier-binding; added by trace.rkt, not expander
   local-mess           ; (listof event)
   ))

;; Empty tokens
(define-tokens prim-tokens
  (prim-module prim-module-begin
   prim-define-syntaxes prim-define-values
   prim-if prim-with-continuation-mark
   prim-begin prim-begin0 prim-#%app prim-lambda
   prim-case-lambda prim-let-values prim-letrec-values 
   prim-letrec-syntaxes+values prim-#%datum prim-#%top prim-stop
   prim-quote prim-quote-syntax prim-require prim-require-for-syntax
   prim-require-for-template prim-provide
   prim-set!
   prim-#%expression
   prim-#%variable-reference
   prim-#%stratified
   prim-begin-for-syntax
   prim-submodule prim-submodule*
   ))

;; ** Signals to tokens

(define signal-mapping
  ;; (number/#f symbol [token-constructor])
  `(;; Emitted from Scheme
    (#f  EOF)
    (#f  error                   ,token-syntax-error)
    (#f  start                   ,token-start)
    (#f  start-top               ,token-start-top)
    (#f  start-ecte              ,token-start-ecte)
    (#f  top-begin               ,token-top-begin)
    (#f  top-non-begin           ,token-top-non-begin)
    (#f  local-remark            ,token-local-remark)
    (#f  local-artificial-step   ,token-local-artificial-step)
    (#f  local-value-binding     ,token-local-value-binding)
    (#f  local-mess              ,token-local-mess)

    ;; Standard signals
    (0   visit                   ,token-visit)
    (1   resolve                 ,token-resolve)
    (2   return                  ,token-return)
    (3   next                    ,token-next)
    (4   enter-list              ,token-enter-list)
    (5   exit-list               ,token-exit-list)
    (6   enter-prim              ,token-enter-prim)
    (7   exit-prim               ,token-exit-prim)
    (8   enter-macro             ,token-enter-macro)
    (9   exit-macro              ,token-exit-macro)
    (10  enter-block             ,token-enter-block)
    (11  splice                  ,token-splice)
    (12  block->list             ,token-block->list)
    (13  next-group              ,token-next-group)
    (14  block->letrec           ,token-block->letrec)
    (16  let-renames             ,token-let-renames)
    (17  lambda-renames          ,token-lambda-renames)
    (19  letrec-syntaxes-renames ,token-letrec-syntaxes-renames)
    (20  phase-up)
    (21  macro-pre-x             ,token-macro-pre-x)
    (22  macro-post-x            ,token-macro-post-x)
    (23  module-body             ,token-module-body)
    (24  block-renames           ,token-block-renames)

    (100 prim-stop)
    (101 prim-module)
    (102 prim-module-begin)
    (103 prim-define-syntaxes)
    (104 prim-define-values)
    (105 prim-if)
    (106 prim-with-continuation-mark)
    (107 prim-begin)
    (108 prim-begin0)
    (109 prim-#%app)
    (110 prim-lambda)
    (111 prim-case-lambda)
    (112 prim-let-values)
    (113 prim-letrec-values)
    (114 prim-letrec-syntaxes+values)
    (115 prim-#%datum)
    (116 prim-#%top)
    (117 prim-quote)
    (118 prim-quote-syntax)
    (119 prim-require)
    (120 prim-require-for-syntax)
    (121 prim-require-for-template)
    (122 prim-provide)
    (123 prim-set!)
    (124 prim-let*-values)
    (125 variable                ,token-variable)
    (126 enter-check             ,token-enter-check)
    (127 exit-check              ,token-exit-check)
    (128 lift-loop               ,token-lift-loop)
    (129 lift-expr               ,token-lift-expr)
    (130 enter-local             ,token-enter-local)
    (131 exit-local              ,token-exit-local)
    (132 local-pre               ,token-local-pre)
    (133 local-post              ,token-local-post)
    (134 lift-statement          ,token-lift-statement)
    (135 module-lift-end-loop    ,token-module-lift-end-loop)
    (136 letlift-loop            ,token-letlift-loop)
    (137 module-lift-loop        ,token-module-lift-loop)
    (138 prim-#%expression)
    (141 start                   ,token-start)
    (142 tag                     ,token-tag)
    (143 local-bind              ,token-local-bind)
    (144 enter-bind              ,token-enter-bind)
    (145 exit-bind               ,token-exit-bind)
    (146 opaque-expr             ,token-opaque-expr)
    (147 rename-list             ,token-rename-list)
    (148 rename-one              ,token-rename-one)
    (149 prim-#%variable-reference)
    (150 lift-require            ,token-lift-require)
    (151 lift-provide            ,token-lift-provide)
    (152 track-origin            ,token-track-origin)
    (153 local-value             ,token-local-value)
    (154 local-value-result      ,token-local-value-result)
    (155 prim-#%stratified)
    (156 prim-begin-for-syntax)
    (157 prepare-env)
    (158 prim-submodule)
    (159 prim-submodule*)
    (160 exit-local-bind)
    (201 start-top               ,token-start-top)))

(define (signal->symbol sig)
  (if (symbol? sig)
      sig
      (cadr (assv sig signal-mapping))))

(define token-mapping (map cdr signal-mapping))

(define (tokenize sig val pos)
  (let ([p (assv sig token-mapping)])
    (cond [(not p)
           (error 'tokenize "bad signal: ~s" sig)]
          [(null? (cdr p))
           (make-position-token sig pos pos)]
          [else
           (make-position-token ((cadr p) val) pos pos)])))
