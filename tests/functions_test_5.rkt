(define (add [x : Integer] [y : Integer]) : Integer (+ x (+ 3 y)))
(define (sub [x : Integer] [y : Integer]) : Integer (- x y))
(add (sub 10 3) (add 5 6))