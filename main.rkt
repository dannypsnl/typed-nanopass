#lang racket

(module+ main
  (require racket/cmdline)

  (define who (make-parameter "world"))
  (command-line
    #:program "racket-project"
    #:once-each
    [("-n" "--name") name "Who to say hello to" (who name)]
    #:args ()
    (printf "hello ~a~n" (who))))

(module+ test
  (require rackunit)

  (define expected 1)
  (define actual 1)

  (test-case
    "Example Test"
    (check-equal? actual expected))

  (test-equal? "Shortcut Equal Test" actual expected))
