(define (func [x : Integer]) : Integer 
    (let ([z 12]) (+ x z)))
(let ([x 24]) (+ 12 (func x)))