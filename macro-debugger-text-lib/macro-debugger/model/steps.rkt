#lang racket/base
(require racket/contract/base
         "stx-util.rkt")
(provide (struct-out protostep)
         (struct-out step)
         (struct-out misstep)
         (struct-out remarkstep)
         (struct-out state)
         (struct-out bigframe)
         reduction-sequence/c
         context-fill
         state-term
         step-term1
         step-term2
         misstep-term1
         bigframe-term
         step-type?
         step-type->string
         rewrite-step?
         rename-step?)

;; A Step is one of
;;  - (step StepType State State)
;;  - (misstep StepType State Exn)
;;  - (remarkstep StepType State (Listof (U String Syntax 'arrow)))
(struct protostep (type s1) #:transparent)
(struct step protostep (s2) #:transparent)
(struct misstep protostep (exn) #:transparent)
(struct remarkstep protostep (contents) #:transparent)

;; A ReductionSequence is (Listof Step)
(define reduction-sequence/c (listof protostep?))

;; A State is (state Stx Stxs Context BigContext Ids Ids Stxs Nat/#f)
(struct state (e foci ctx lctx binders uses frontier seq) #:transparent)

;; A Context is (Listof Frame)
;; A Frame is (Syntax -> Syntax)

;; A BigContext is (list-of BigFrame)
;; A BigFrame is (make-bigframe Context Syntaxes Syntax)
(struct bigframe (ctx foci e))

;; context-fill : Context Syntax -> Syntax
(define (context-fill ctx stx)
  (datum->artificial-syntax
   (let loop ([ctx ctx] [stx stx])
     (if (null? ctx)
         stx
         (let ([frame0 (car ctx)])
           (loop (cdr ctx) (frame0 stx)))))))

(define (state-term s)
  (context-fill (state-ctx s) (state-e s)))

(define (step-term1 s)
  (state-term (protostep-s1 s)))
(define (step-term2 s)
  (state-term (step-s2 s)))

(define (misstep-term1 s)
  (state-term (protostep-s1 s)))

(define (bigframe-term bf)
  (context-fill (bigframe-ctx bf) (bigframe-e bf)))

;; A StepType is a Symbol in the following alist.

(define step-type-meanings
  '((macro            . "Macro transformation")

    (sync             . "Sync with expander")

    (rename-lambda    . "Rename formal parameters")
    (rename-letX      . "Rename bound names")
    (rename-block     . "Introduce scope for internal definition context")
    (rename-module    . "Introduce scope for module")
    (rename-mod-shift . "Shift the self module-path-index")
    (rename-modbeg    . "Introduce scope for module body")
    (lsv-remove-syntax . "Remove syntax bindings")

    (resolve-variable . "Resolve variable (remove extra marks)")
    (tag-module-begin . "Tag #%module-begin")
    (tag-app          . "Tag application")
    (tag-datum        . "Tag datum")
    (tag-top          . "Tag top-level variable")
    (capture-lifts    . "Capture lifts")
    (provide          . "Expand provide-specs")

    (local-lift       . "Macro lifted expression to top-level")
    (module-lift      . "Macro lifted declaration to end of module")
    (block->letrec    . "Transform block to letrec")
    (finish-letrec    . "Finish letrec")
    (splice-block     . "Splice block-level begin")
    (splice-module    . "Splice module-level begin")
    (splice-lifts     . "Splice definitions from lifted expressions")
    (splice-end-lifts . "Splice lifted module declarations")

    (remark           . "Macro made a remark")
    (track-origin     . "Macro called syntax-track-origin")

    (error            . "Error")))

(define (step-type->string x)
  (cond [(assq x step-type-meanings) => cdr]
        [(string? x) x]
        [else (error 'step-type->string "not a step type: ~s" x)]))

(define step-type?
  (let ([step-types (map car step-type-meanings)])
    (lambda (x)
      (and (memq x step-types) #t))))

(define (rename-step? x)
  (memq (protostep-type x) 
        '(rename-lambda
          rename-letX
          rename-block
          rename-module
          rename-mod-shift
          rename-modbeg
          track-origin)))

(define (rewrite-step? x)
  (and (step? x) (not (rename-step? x))))
