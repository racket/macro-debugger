#lang racket/base
(require racket/class
         racket/format
         racket/list
         racket/snip
         racket/draw
         racket/math
         "base.rkt")
(provide steps-to-arrow-snip%
         snip-class)

(define steps-to-arrow-snip%
  (class one-cell-snip%
    (init [style #f])
    (inherit set-style get-style get/cache-extent set-snipclass
             get-text-pen-color draw-background)
    (super-new [text-for-extent "ZZZ"])
    (set-snipclass snip-class)
    (send (get-the-snip-class-list) add snip-class)
    (when style (set-style style))

    (define/override (draw dc x y left top right bottom dx dy caret)
      (define-values (w h d _a) (get/cache-extent dc))
      ;(begin (define A (* 1/3 h)) (define B (* 1/6 h)) (define C (/ d -2.0)))
      ;(begin (define A (* 1/4 h)) (define B (* 1/6 h)) (define C 0 #; (/ d -2.0)))
      (begin (define A (* 1/6 h)) (define B (* 1/8 h)) (define C (/ d -2.0)))
      (define (X wf) (+ x (* w wf 1/3)))
      (define (Y af bf) (+ y h C (* -1 af A) (* -1 bf B)))
      (define (P wf af bf) (cons (X wf) (Y af bf)))
      (let ([saved-pen (send dc get-pen)]
            [saved-brush (send dc get-brush)]
            [saved-smoothing (send dc get-smoothing)]
            [fg-color (get-text-pen-color dc caret)])
        (begin
          #;(draw-background dc x y w h caret)
          (send dc set-brush "red" 'solid)
          (send dc set-smoothing 'aligned)
          (send dc set-pen (make-pen #:color fg-color #:width 1))
          (send dc draw-polygon
                (list (P 0.2 1 2) (P 1.8 1 2) (P 1.8 2 2) (P 2.8 1 1)
                      (P 1.8 0 0) (P 1.8 1 0) (P 0.2 1 0) (P 0.2 1 2))))
        (send dc set-brush saved-brush)
        (send dc set-pen saved-pen)
        (send dc set-smoothing saved-smoothing)))

    (define/override (get-whole-text) "→")
    ))

(define steps-to-arrow-snip-class%
  (class snip-class%
    (inherit set-classname set-version)
    (super-new)

    (set-classname (~s '(lib "steps-to-arrow.rkt" "macro-debugger" "syntax-browser" "icons")))
    (set-version 1)

    (define/override (read f)
      (new steps-to-arrow-snip%))
    ))

(define snip-class (new steps-to-arrow-snip-class%))
