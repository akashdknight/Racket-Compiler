(define (add_sp [x : Integer] [y : Integer]) : Integer 
    (if (eq? x 0)
        y
        (add_sp (- x 1) (+ x y))))
(add_sp 5 0)