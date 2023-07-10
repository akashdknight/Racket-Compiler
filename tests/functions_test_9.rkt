(define (lesser [x : Integer] [y : Integer]) : Integer (if (< x y) x y))
(let ([x 42]) (let ([y 56]) (lesser x y)))