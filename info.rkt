#lang info
(define collection "racket-project")
(define deps '("base"))
(define build-deps '("rackunit-lib"
                     "scribble-lib" "racket-doc"
                     ; coverage
                     "cover" "cover-badge"))
(define scribblings '(("scribblings/racket-project.scrbl" ())))
(define pkg-desc "Description Here")
(define version "0.0")
(define license '(Apache-2.0 OR MIT))
(define pkg-authors '(dannypsnl))
