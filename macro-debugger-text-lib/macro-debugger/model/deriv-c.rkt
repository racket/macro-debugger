#lang racket/base
(provide (all-defined-out))

;; PrepareExpEnv = (listof LocalAction)

;; A Node(a) is:
;;   (make-node a ?a)
(define-struct node (z1 z2) #:transparent)

;; A TopDeriv is one of
;;   (make-lift-deriv <Node(Stx)> Deriv Stxs TopDeriv)
;;   Deriv

;; A Deriv is one of
;;   MRule
;;   PrimDeriv

;; Base = << Node(Stx) Rs ?exn >>

(define-struct (deriv node) () #:transparent)
(define-struct (base deriv) (resolves ?1) #:transparent)

(define-struct (lift-deriv deriv) (first lift-stx second) #:transparent)
(define-struct (tagrule deriv) (tagged-stx next) #:transparent)

;; A DerivLL is one of
;;   (make-lift/let-deriv <Node(Stx)> Deriv Stx Deriv)
;;   Deriv
(define-struct (lift/let-deriv deriv) (first lift-stx second) #:transparent)

;; A MRule is
;;   (make-mrule <Base(Stx)> ?Stx (listof LocalAction) ?exn ?Stx ?Deriv)
(define-struct (mrule base) (me1 locals me2 ?2 etx next) #:transparent)

;; A LocalAction is one of:
(define-struct local-exn (exn) #:transparent)
(define-struct (local-expansion node) (for-stx? me1 inner lifted me2 opaque)
  #:transparent)
(define-struct local-lift (expr ids) #:transparent)
(define-struct local-lift-end (decl) #:transparent)
(define-struct local-lift-require (req expr mexpr) #:transparent)
(define-struct local-lift-provide (prov) #:transparent)
(define-struct local-bind (names ?1 renames bindrhs) #:transparent)
(define-struct local-value (name ?1 resolves bound? binding) #:transparent)
  ;; binding is saved (identifier-binding name) at time of lookup, since it may change
  ;; if name is rebound in definition context
(define-struct track-origin (before after) #:transparent)
(define-struct local-remark (contents) #:transparent)
  ;; contents : (listof (U string syntax))
(define-struct local-mess (events) #:transparent)

;; A PrimDeriv is one of
(define-struct (prule base) () #:transparent)
(define-struct (p:variable prule) () #:transparent)

;;   (make-p:module <Base> PrepareEnv stxes ?Deriv ?exn ?stx ?Deriv ?exn Deriv ?stx)
;;   (make-p:#%module-begin <Base> Stx ModuleBegin/Phase ?exn)
(define-struct (p:module prule) (prep rename check1 ?2 tag2 check2 ?3 body shift)
  #:transparent)
(define-struct (p:#%module-begin prule) (me pass12 ?2 pass3 ?3 pass4) #:transparent)

;;   (make-p:define-syntaxes <Base> (listof LocalAction) DerivLL (listof LocalAction))
;;   (make-p:define-values <Base> Deriv)
(define-struct (p:define-syntaxes prule) (prep rhs locals) #:transparent)
(define-struct (p:define-values prule) (rhs) #:transparent)

;;   (make-p:#%expression <Base> Deriv ?Stx)
;;   (make-p:if <Base> Boolean Deriv Deriv Deriv)
;;   (make-p:wcm <Base> Deriv Deriv Deriv)
;;   (make-p:set! <Base> Rs ?Exn Deriv)
;;   (make-p:set!-macro <Base> Rs Deriv)
(define-struct (p:#%expression prule) (inner untag) #:transparent)
(define-struct (p:if prule) (test then else) #:transparent)
(define-struct (p:wcm prule) (key mark body) #:transparent)
(define-struct (p:set! prule) (id-resolves ?2 rhs) #:transparent)
(define-struct (p:set!-macro prule) (deriv) #:transparent)

;;   (make-p:#%app <Base> Stx Derivs)
;;   (make-p:begin <Base> Derivs)
;;   (make-p:begin0 <Base> Derivs)
(define-struct (p:#%app prule) (derivs) #:transparent)
(define-struct (p:begin prule) (derivs) #:transparent)
(define-struct (p:begin0 prule) (derivs) #:transparent)

;;   (make-p:lambda <Base> LambdaRenames BDeriv)
;;   (make-p:case-lambda <Base> (list-of CaseLambdaClause))
;;   (make-p:let-values <Base> LetRenames (list-of Deriv) BDeriv)
;;   (make-p:letrec-values <Base> LetRenames (list-of Deriv) BDeriv)
;;   (make-p:letrec-syntaxes+values <Base> LSVRenames PrepareExpEnv
;;      (list-of BindSyntaxes) (list-of Deriv) BDeriv)
(define-struct (p:lambda prule) (renames body) #:transparent)
(define-struct (p:case-lambda prule) (renames+bodies) #:transparent)
(define-struct (p:let-values prule) (renames rhss body) #:transparent)
(define-struct (p:letrec-values prule) (renames rhss body) #:transparent)
(define-struct (p:letrec-syntaxes+values prule)
  (srenames prep sbindrhss vrhss body)
  #:transparent)

;;   (make-p:provide <Base> (listof Deriv) ?exn)
(define-struct (p:provide prule) (inners ?2) #:transparent)

;;   (make-p:require <Base> (listof LocalAction))
(define-struct (p:require prule) (locals) #:transparent)

(define-struct (p:submodule prule) (exp locals) #:transparent)
(define-struct (p:submodule* prule) (exp locals) #:transparent)

;;   (make-p:#%stratified-body <Base> BDeriv)
(define-struct (p:#%stratified-body prule) (bderiv) #:transparent)

;;   (make-p:begin-for-syntax <base> (listof LocalAction) BFSBody)
;;     where BFSBody is one of
;;       - ModuleBegin/Phase
;;       - (list BeginForSyntaxLifts ... LDeriv))
(define-struct (p:begin-for-syntax prule) (prep body locals) #:transparent)

;;   (make-p:stop <Base>)
;;   (make-p:unknown <Base>)
;;   (make-p:#%top <Base> Stx)
;;   (make-p:#%datum <Base> Stx)
;;   (make-p:quote <Base>)
;;   (make-p:quote-syntax <Base>)
;;   (make-p:#%variable-reference <Base>)
(define-struct (p::STOP prule) () #:transparent)
(define-struct (p:stop p::STOP) () #:transparent)
(define-struct (p:unknown p::STOP) () #:transparent)
(define-struct (p:#%top p::STOP) () #:transparent)
(define-struct (p:#%datum p::STOP) () #:transparent)
(define-struct (p:quote p::STOP) () #:transparent)
(define-struct (p:quote-syntax p::STOP) () #:transparent)
(define-struct (p:#%variable-reference p::STOP) () #:transparent)

;;   (p:declare <Base>)
(struct p:declare prule () #:transparent)

;; A LDeriv is
;;   (make-lderiv <Node(Stxs)> ?exn (list-of Deriv))
(define-struct (lderiv node) (?1 derivs) #:transparent)

;; A BDeriv is
;;   (make-bderiv <Node(Stxs)> BlockRenames (list-of BRule) (U LDeriv BlockLetrec))
(define-struct (bderiv node) (renames pass1 pass2) #:transparent)

;; A BlockLetrec is
;;   (block:letrec Syntax (Listof Deriv) LDeriv)
(define-struct block:letrec (stx rhss lderiv) #:transparent)

;; A BRule is one of
;;   (make-b:error exn)
;;   (make-b:expr Deriv)
;;   (make-b:splice Deriv ?exn Stxs ?exn)
;;   (make-b:defvals Deriv ?exn Stx ?exn)
;;   (make-b:defstx Deriv ?exn Stx ?exn PrepareExpEnv BindSyntaxes)
(define-struct brule () #:transparent)
(define-struct (b:error brule) (?1) #:transparent)
(define-struct (b:expr brule) (head) #:transparent)
(define-struct (b:splice brule) (head ?1 tail ?2) #:transparent)
(define-struct (b:defvals brule) (head ?1 rename ?2) #:transparent)
(define-struct (b:defstx brule) (head ?1 rename ?2 prep bindrhs) #:transparent)

;; A BindSyntaxes is
;;   (make-bind-syntaxes DerivLL (listof LocalAction))
(define-struct bind-syntaxes (rhs locals) #:transparent)

;; A CaseLambdaClause is
;;   (make-clc ?exn CaseLambdaRename BDeriv)
(define-struct clc (?1 renames body) #:transparent)

;; A BlockRename is (cons Stx Stx)

;; A BeginForSyntaxLifts is
;;   (make-bfs:lift LDeriv (listof stx))
(define-struct bfs:lift (lderiv lifts) #:transparent)

;; A ModuleBegin/Phase is (module-begin/phase ModulePass1 ModulePass2 ModulePass3)
(define-struct module-begin/phase (pass1 pass2 pass3) #:transparent)

;; A ModPass1 is (list-of ModRule1)
;; A ModPass2 is (list-of ModRule2)
;; A ModPass3 is (list-of p:provide)

;; A ModRule1 is one of 
;;   (make-mod:prim ModPass1Head ModPass1Prim)
;;   (make-mod:lift-end Stxs)
;; A ModPass1Head is one of
;; - Deriv
;; - (modp1:lift Deriv Syntaxes Syntaxes Syntaxes ModPass1)
;; A ModPass1Prim is one of
;; - (modp1:splice ?Exn Syntaxes)
;; - p:begin-for-syntax, p:define-values, p:define-syntaxes, p:require
;; - p:submodule, p:declare
;; - p:stop
(struct mod:lift-end (ends) #:transparent)
(struct modp1:prim (head prim) #:transparent)
(struct modp1:lift (head lifted-defs lifted-reqs lifted-mods mods) #:transparent)
(struct modp1:splice (?1 tail) #:transparent)

;; A ModRule2 is one of
;; - (mod:lift-end Stxs)
;; - (modp2:skip)
;; - (modp2:cons Deriv LocalActions)
;; - (modp2:lift Deriv LocalActions Syntaxes Syntaxes Syntaxes ModP2Submods ModPass2)
(struct modp2:skip () #:transparent)
(struct modp2:cons (deriv locals) #:transparent)
(struct modp2:lift (deriv locals lifted-reqs lifted-mods lifted-defs mods defs) #:transparent)

;; A ModP2Submod is one of
;; - #f
;; - p:submodule

;; A ModRule3 is one of
;; - #f
;; - (modp34:bfs (Listof ModRule3))
;; - p:provide
(struct modp34:bfs (subs) #:transparent)

;; A ModRule4 is one of
;; - #f
;; - (modp34:bfs (Listof ModRule4))
;; - p:submodule*


;; ECTE represents expand/compile-time-evals
;; (make-ecte stx ?stx (listof LocalAction) Deriv Deriv (listof LocalAction))

(define-struct (ecte deriv) (locals first second locals2) #:transparent)
