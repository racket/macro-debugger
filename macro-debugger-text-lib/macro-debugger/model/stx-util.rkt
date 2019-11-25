#lang racket/base
(require (for-syntax racket/base)
         syntax/stx)
(provide syntax-e*
         stx->list*
         stx->datum
         syntaxish?)

;; Update for syntax taint: On get, disarm stx on the way, but don't
;; disarm final stx. On replace, disarm and rearm along the way.

(define (stx-disarm stx)
  (if (syntax? stx) (syntax-disarm stx #f) stx))

;;(define (stx-car* stx) (stx-car (stx-disarm stx)))
;;(define (stx-cdr* stx) (stx-cdr (stx-disarm stx)))

(define (syntax-e* stx) (syntax-e (stx-disarm stx)))

(define (stx->list* stx)
  (if (stx-list? stx)
      (let loop ([stx stx])
        (cond [(syntax? stx)
               (loop (syntax-e* stx))]
              [(pair? stx)
               (cons (car stx) (loop (cdr stx)))]
              [else stx]))
      #f))

;; ----

(define (stx->datum x)
  (syntax->datum (datum->syntax #f x)))

(define (syntaxish? x)
  (or (syntax? x)
      (null? x)
      (and (pair? x)
           (syntaxish? (car x))
           (syntaxish? (cdr x)))))
