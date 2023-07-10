(define (add [x : Integer] [y : Integer]) : Integer (+ x (+ 2 y)))
(define (addsp [x : Integer] [y : Integer]) : Integer (if (and (> x 0) (> y 0))
                                                        (+ x y)
                                                        (- (+ x y) 2)))
(addsp (add 2 5) (add -6 8))