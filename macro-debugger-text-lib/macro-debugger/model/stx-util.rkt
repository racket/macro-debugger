#lang racket/base
(provide stx->datum
         syntaxish?
         stx-disarm
         resyntax
         restx
         syntax-armed?
         syntax-armed/tainted?
         syntax-unarmed?
         property:unlocked-by-expander
         property:artificial
         datum->artificial-syntax
         syntax-artificial?)

(define (stx->datum x)
  (syntax->datum (datum->syntax #f x)))

(define (syntaxish? x)
  (or (syntax? x)
      (null? x)
      (and (pair? x)
           (syntaxish? (car x))
           (syntaxish? (cdr x)))))

(define insp
  (variable-reference->module-declaration-inspector
   (#%variable-reference)))

(define (stx-disarm stx)
  (if (syntax? stx) (syntax-disarm stx insp) stx))

(define (resyntax v stx [dstx (stx-disarm stx)] #:rearm? [rearm? #t])
  (unless (and (syntax? stx) (syntax? dstx))
    (error 'resyntax "not syntax: ~e, ~e" stx dstx))
  (define stx* (mark-artificial (datum->syntax dstx v stx stx)))
  (if rearm? (syntax-rearm stx* stx) stx*))

(define (restx v stx [dstx (stx-disarm stx)] #:rearm? [rearm? #t])
  (if (syntax? stx) (resyntax v stx dstx #:rearm? rearm?) v))

(define (syntax-armed? stx)
  (and (not (syntax-tainted? stx))
       (syntax-tainted? (datum->syntax stx #f))))

(define (syntax-armed/tainted? stx)
  (syntax-tainted? (datum->syntax stx #f)))

(define (syntax-unarmed? stx)
  (not (syntax-armed/tainted? stx)))

;; Used to communicate with syntax-browser
(define property:unlocked-by-expander (gensym 'unlocked-by-expander))
(define property:artificial (gensym 'artificial))

(define (mark-artificial stx)
  (syntax-property stx property:artificial #t))

(define (datum->artificial-syntax x)
  (define (loop x)
    (cond [(pair? x) (mark-artificial (datum->syntax #f (tailloop x)))]
          [(syntax? x) x]
          [else (mark-artificial (datum->syntax #f x))]))
  (define (tailloop x)
    (cond [(pair? x) (cons (loop (car x)) (tailloop (cdr x)))]
          [else (loop x)]))
  (loop x))

(define (syntax-artificial? stx)
  (syntax-property stx property:artificial))
