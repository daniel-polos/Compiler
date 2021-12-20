(define d (lambda x (cons x x)))
(let* . (((a (lambda (x . (y)) . (a x) )) . ((c `,(d)))) . ((if (a (begin (and)) 'a) `(,@c (a a))))))
