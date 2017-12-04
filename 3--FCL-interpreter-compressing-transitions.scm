;;; FCL, without calls (_not_ FCL*)
;;; made to look just as the specializer will.
(use-modules (grand scheme))

(define variable? symbol?)
(define (constant? x) (or (boolean? x) (number? x) (null? x)))

(define (update store variable value)
  (match store
    [() `((,variable . ,value))]
    [((var . val) . store*)
     (if (eq? var variable)
         `((,var . ,value) . ,store*)
         `((,var . ,val) . ,(update store* variable value)))]))

(define (eval-expr e store)
  (match e
    [(? constant?) e]
    [(? variable?) (assoc-ref store e)]
    [('quote e*) e*]
    [(op . es) (eval-application op (map (lambda (e) (eval-expr e store)) es))]))

(define (eval-application rator rands)
  (match `(,rator . ,rands)
    [('car (h . _)) h]
    [('cdr (_ . t)) t]
    [('cons h t) `(,h . ,t)]
    [('= e e) #t]
    [('= _ _) #f]
    [('+ m n) (+ m n)]
    [('- m n) (- m n)]
    [('* m n) (* m n)]
    [('/ m n) (/ m n)]
    [('% m n) (modulo m n)]))


(define (run-block block store blocks-map) ;;-> Either (succ, store) ('HALT, value)
  (match block
    [(('return e))
     `(HALT ,(eval-expr e store))]
    [(('goto l))
     (run-block (blocks-map l) store blocks-map)]
    [(('if e l l*))
     `(,(if (eval-expr e store) l l*) ,store)]
    [((x ':= e) . block*)
     (run-block block* (update store x (eval-expr e store)) blocks-map)]))


(define (run label store blocks-map) ;; -> value
  (match (run-block (blocks-map label) store blocks-map)
    [('HALT result) result]
    [(label* store*) (run label* store* blocks-map)]))

  
(define (interpret program input-values)
  (and-let* ([(input-names
               init-label
               . blocks) program]
             [blocks-map (lambda (l) (assoc-ref blocks l))]
             [initial-store (map cons input-names input-values)])
    (run init-label initial-store blocks-map)))


;;; FCL example
(define example-pow
  '[ (m n) 
     pow

     (pow [res := 1]
          [goto test])

     (test [if (= n 0) end loop])

     (loop [res := (* res m)]
           [n := (- n 1)]
           [goto test])

     (end [return res]) ])
  
[e.g. (interpret example-pow '(2 3))  ===> 8]



(define example-stck
  '((formula inputs)
    init
    (init [stck := inputs]
          [cmd := (car formula)]
          [cnt := (cdr formula)]
          [goto test-cmd])
    (test-cmd [if (= cmd '+) add test-cmd*])
    (test-cmd* [if (= cmd '*) mul test-cmd**])
    (test-cmd** [if (= cmd '-) sub test-cmd***])
    (test-cmd*** [if (= cmd 'DUP) dup test-cmd****])
    (test-cmd**** [if (= cmd 'SWAP) swap error])
    (add [a := (car stck)]
         [stck := (cdr stck)]
         [b := (car stck)]
         [stck := (cdr stck)]
         [stck := (cons (+ b a) stck)]
         [goto next])
    (mul [a := (car stck)]
         [stck := (cdr stck)]
         [b := (car stck)]
         [stck := (cdr stck)]
         [stck := (cons (* b a) stck)]
         [goto next])
    (sub [a := (car stck)]
         [stck := (cdr stck)]
         [b := (car stck)]
         [stck := (cdr stck)]
         [stck := (cons (- b a) stck)]
         [goto next])
    (dup [a := (car stck)]
         [stck := (cons a stck)]
         [goto next])
    (swap [a := (car stck)]
          [stck := (cdr stck)]
          [b := (car stck)]
          [stck := (cdr stck)]
          [stck := (cons b (cons a stck))]
          [goto next])
    (next [if (= cnt ()) halt step])
    (step [cmd := (car cnt)]
          [cnt := (cdr cnt)]
          [goto test-cmd])
    (halt [return (car stck)])
    (error [return 'ERROR])))


[e.g. (interpret example-stck '((DUP * SWAP DUP * +) (3 4)))  ===> 25]
