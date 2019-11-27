#lang racket/base
(provide stx->datum
         syntaxish?
         stx-disarm
         resyntax
         restx)

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
  (define stx* (datum->syntax dstx v stx stx))
  (if rearm? (syntax-rearm stx* stx) stx*))

(define (restx v stx [dstx (stx-disarm stx)] #:rearm? [rearm? #t])
  (if (syntax? stx) (resyntax v stx dstx #:rearm? rearm?) v))
