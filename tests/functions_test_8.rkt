(define (blah [x : Integer]) : Integer
    (let ([y (and #t #f)]) (if y (+ 23 x) (- x 10))))
(let ([x (blah 32)]) (+ x (blah 12)))