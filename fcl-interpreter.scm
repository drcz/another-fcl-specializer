(use-modules (grand scheme))
(define (zip xs ys) (map cons xs ys))

(define variable? symbol?)
(define (constant? x) (or (boolean? x) (number? x)))
                          
(define (update store variable value)
  (match store
    [() `((,variable . ,value))]
    [((var . val) . store*)
     (if (eq? var variable)
         `((,var . ,value) . ,store*)
         `((,var . ,val) . ,(update store* variable value)))]))

(define (value e store)
  (match e
    [(? constant?) e]
    [(? variable?) (assoc-ref store e)]
    [('quote e*) e*]
    [(op . es) (application op (map (lambda (e) (value e store)) es))]))

(define (application rator rands)
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

(define (run program input-values)  
  (let* ([(input-variables initial-label . blocks) program]
         [initial-store (zip input-variables input-values)]
         [blocks-map (lambda (label) (assoc-ref blocks label))])
    (let run ([block (blocks-map initial-label)]
              [store initial-store])
      (match block
        [(('goto l)) (run (blocks-map l) store)]
        [(('return e)) (value e store)]
        [(('if e l l*)) (run (blocks-map (if (value e store) l l*)) store)]
        [((v ':= ('call l . _)) . block*) (run block* (update store v (run (blocks-map l) store)))] ;;; Gluck's FCL*.
        [((v ':= e) . block*) (run block* (update store v (value e store)))]))))

;;; FCL example
[e.g. (run '[ (m n) 
              pow

              (pow (res := 1)
                   (goto test))
              (test (if (= n 0) end loop))
              (loop (res := (* res m))
                    (n := (- n 1))
                    (goto test))
              (end (return res)) ]
           '(2 3))
      ===> 8]

;;; FCL* example
[e.g. (run '[ (m n)
              ack

              (ack (if (= m 0) done next))
              (next (if (= n 0) ack0 ack1))
              (done (return (+ n 1)))              
              (ack0 (n := 1)
                    (goto ack2))
              (ack1 (n := (- n 1))
                    (n := (call ack m n))
                    (goto ack2))
              (ack2 (m := (- m 1))
                    (n := (call ack m n))
                    (return n)) ]
           '(2 3))
      ===> 9]


