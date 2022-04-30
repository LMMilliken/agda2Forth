(import (only (chezscheme) record-case))

(define (A) (begin (display "encountered axiom: A\n") (exit 1)))

(define (id) (lambda (a) a))

(define (true) (list 'true))

(define (false) (list 'false))

(define (not) (lambda (a) (record-case a ((true) () (false))
((false) () (true)))))

(define 
  (ite)
  (lambda (a) (lambda (b) (lambda (c) (lambda (d) (record-case b ((true) () c)
((false) () d)))))))

(define (loop) (loop))

(define (test1) (((((ite) (list)) (false)) (loop)) (true)))

(define (zero) (list 'zero))

(define (suc) (lambda (a) (list 'suc a)))

(define (one) ((suc) (zero)))

(define (two) ((suc) (one)))

(define (three) ((suc) (two)))

(define (pred) (lambda (a) (record-case a ((zero) () a)
((suc) (b) b))))

(define (_+_) (lambda (a) (lambda (b) (record-case a ((zero) () b)
((suc) (c) ((suc) (((_+_) c) b)))))))

(define (twice) (lambda (a) (record-case a ((zero) () a)
((suc) (b) ((suc) ((suc) ((twice) b)))))))

(define (pow2) (lambda (a) (record-case a ((zero) () ((suc) a))
((suc) (b) ((twice) ((pow2) b))))))

(define (consume) (lambda (a) (record-case a ((zero) () a)
((suc) (b) ((consume) b)))))

(define (test2) ((consume) ((pow2) ((twice) ((twice) ((twice) (three)))))))

(define (nil) (list 'nil))

(define (con) (lambda (a) (lambda (b) (lambda (c) (list 'con a
b
c)))))

(define (head) (lambda (a) (lambda (b) (lambda (c) (record-case c ((con) (d e f) e))))))

(define (tail) (lambda (a) (lambda (b) (lambda (c) (record-case c ((con) (d e f) f))))))

(define 
  (map)
  (lambda 
    (a)
    (lambda 
      (b)
      (lambda 
        (c)
        (lambda 
          (d)
          (lambda 
            (e)
            (record-case e ((nil) () e)
((con) (f g h) ((((con) f) (d g)) ((((((map) (list)) (list)) (list)) d) h))))))))))

(define 
  (test3)
  ((((head) (list)) (list)) 
    ((((tail) (list)) (list)) 
      ((((((map) (list)) (list)) (list)) (suc)) 
        ((((con) ((suc) ((suc) (zero)))) (zero)) ((((con) ((suc) (zero))) ((suc) (zero))) ((((con) (zero)) ((suc) ((suc) (zero)))) (nil))))))))

(define (z123\x27;\x23;\x7C;H\x5C;x65llo) (zero))

(define (test4) (z123\x27;\x23;\x7C;H\x5C;x65llo))

(define (fie) (lambda (a) ((suc) a)))

(define (foe) (lambda (a) ((suc) ((fie) a))))

(define (fun) (((_+_) ((fie) ((suc) ((suc) (zero))))) ((foe) ((suc) ((suc) (zero))))))