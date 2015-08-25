#lang info

(define collection 'multi)

(define deps '("base"
               "class-iop-lib"
               "compatibility-lib"
               "data-lib"
               "gui-lib"
               "images-lib"
               "images-gui-lib"
               "parser-tools-lib"
               "unstable-lib"
               "macro-debugger-text-lib"
               ("draw-lib" #:version "1.7")))
(define build-deps '("racket-index"
                     "rackunit-lib"
                     "scribble-lib"
                     "racket-doc"
                     "unstable-doc"))

(define pkg-desc "The macro debugger tool")

(define pkg-authors '(ryanc))
