#lang racket/base
(require (for-syntax racket/base))
(provide id
         pre-id
         leid
         lift
         mklist
         liftmod
         liftend
         wrong
         Tid
         Tlist
         Tlet
         Tleid
         Tlift
         myor
         the-current-output-port)

(define-syntax (id stx)
  (syntax-case stx ()
    [(id x) #'x]))

(define-syntax (pre-id stx)
  (syntax-case stx ()
    [(pre-id x) #'(id x)]))

(define-syntax (leid stx)
  (syntax-case stx ()
    [(leid e)
     (with-syntax ([ee (local-expand #'e 'expression null)])
       #`(#%expression ee))]))

(define-syntax (lift stx)
  (syntax-case stx ()
    [(lift e)
     (with-syntax ([v (syntax-local-lift-expression #'e)])
       #'(#%expression v))]))

(define-syntax (mklist stx)
  (syntax-case stx ()
    [(mklist k v)
     (with-syntax ([mk (syntax-local-lift-require
                        #'(only racket/list make-list)
                        #'make-list)])
       #'(#%plain-app mk k v))]))

(define-syntax (liftmod stx)
  (syntax-case stx ()
    [(lmod mod e2)
     (begin
       (syntax-local-lift-module #'mod)
       #'e2)]))

(define-syntax (liftend stx)
  (syntax-case stx ()
    [(_ decl e2)
     (begin
       (syntax-local-lift-module-end-declaration #'decl)
       #'e2)]))

(define-syntax (wrong stx)
  (raise-syntax-error #f "macro blows up here!" stx))

(define-syntax (Tid stx)
  (syntax-case stx ()
    [(Tid e) #'e]))

(define-syntax (Tlist stx)
  (syntax-case stx ()
    [(Tlist e) #'(list e)]))

(define-syntax (Tlet stx)
  (syntax-case stx ()
    [(Tlet x e b) #'((lambda (x) b) e)]))

(define-syntax Tleid (syntax-local-value #'leid))
(define-syntax Tlift (syntax-local-value #'lift))

;; (define-syntax (Tleid stx)
;;   (syntax-case stx ()
;;     [(Tleid e)
;;      (with-syntax ([ee (local-expand #'e 'expression null)])
;;        #`(#%expression ee))]))

;; (define-syntax (Tlift stx)
;;   (syntax-case stx ()
;;     [(Tlift e)
;;      (with-syntax ([v (syntax-local-lift-expression #'e)])
;;        #'(#%expression v))]))

(define-syntax (myor stx)
  (syntax-case stx ()
    [(myor x)
     #'x]
    [(myor x y ...)
     #'(let ((t x))
         (if t t (myor y ...)))]))

(define-syntax the-current-output-port
  (make-set!-transformer
   (lambda (stx)
     (syntax-case stx (set!)
       [(set! the-current-output-port op)
        #'(#%plain-app current-output-port op)]))))
