(add-to-load-path (getcwd))
(include-from-path "3--FCL-interpreter-compressing-transitions.scm")

(define (forget store variable) ; :: store -> store
  (match store
    [() '()]
    [((var . val) . store*)
     (if (eq? var variable)
         store*
         `((,var . ,val) . ,(forget store* variable)))]))


(define (ground-expression? e)
  (match e ;;; just free of vars, for now
    [(? constant?) #t]
    [('quote e) #t]
    [_ #f]))

;;; now analogs of eval-expr and stuff...
(define (residualized e meta-store)
  (match e
    [(? constant?)
     e]
    [('quote _)
     e]
    [(? variable?)
     (match (assoc-ref meta-store e)
       [#f e]
       [(? constant? c) c]
       [val `(quote ,val)])]
    [(op . es)
     (residual-application op (map (lambda (e) (residualized e meta-store)) es))]))


(define (not-unifiable? e e*)
  (match `(,e ,e*) ;;; TODO also add embedded-test from budda/pindol [?]
    [(e e) #f]
    [((? variable?) _) #f]
    [(_ (? variable?)) #f]
    [((? number?) ('quote _)) #f]
    [(('quote _) (? number?)) #f]
    [(('cons h t) ('cons h* t*)) (or (not-unifiable? h h*) (not-unifiable? t t*))]
    [(('cons _ _) ('quote (_ . _))) #f]
    [(('quote (_ . _)) ('cons _ _)) #f]
    [(('cons h t) _) #t]
    [(_ ('cons h t)) #t]
    [_ #f]))


(define (residual-application rator rands)
  (if (every ground-expression? rands)
      (match (eval-expr `(,rator . ,rands) '())
        [(? constant? c) c]
        [expr `(quote ,expr)])
      ;; else:
      (match `(,rator . ,rands)
        [('car ('cons h _)) h]
        [('cdr ('cons _ t)) t]
        [('cons ('car x) ('cdr x)) x]
        [('= e e) #t]
        [('= e e*) (if (not-unifiable? e e*) #f `(= ,e ,e*))] ;; !
        [('+ e e) `(* 2 ,e)]
        [('+ n 0) n]
        [('+ 0 n) n]
        [('- n n) 0]
        [('- n 0) n]
        [('* 0 _) 0]
        [('* _ 0) 0]
        [('* n 1) n]
        [('* 1 n) n]
        [('/ n 1) n]
        [('/ n n) 1]
        [('/ 0 _) 0]
        [('% 0 _) 0]
        [('% n 1) n]
        [expr expr])))

[e.g. (residualized '(cons (+ x 3) (cdr xs)) '())
      ===> (cons (+ x 3) (cdr xs))]
[e.g. (residualized '(cons (+ x 3) (cdr xs)) '([xs . (q w e)]))
      ===> (cons (+ x 3) '(w e))]
[e.g. (residualized '(cons (car (cons 'a ys)) (cdr (cons 'b xs))) '())
      ===> (cons 'a xs)]
[e.g. (residualized '(+ (* x (- y y)) (* 3 (/ z z))) '()) ===> 3]


(define (new-label #;for label meta-store) `(,label ,meta-store))

(define (seen-before? label block) (member? label (map car block)))

(define (drive-block block meta-store blocks-map) ;; -> residual-block
  (match block
    [(['return e])
     `([return ,(residualized e meta-store)])]

    [(['goto l])
     (drive-block (blocks-map l) meta-store blocks-map)]

    [(['if e l l*])
     (match (residualized e meta-store)
       [(? ground-expression? ge)
        (if (eval-expr ge '())
            (drive-block (blocks-map l) meta-store blocks-map)
            (drive-block (blocks-map l*) meta-store blocks-map))]
       [e*
        `([if ,e* ,(new-label l meta-store) ,(new-label l* meta-store)])])]

    [([x ':= e] . block*)
     (match (residualized e meta-store)
       [(? ground-expression? ge)
        (drive-block block* (update meta-store x (eval-expr ge '())) blocks-map)]
       [e* ;; not very general, but...
        `([,x := ,e*] . ,(drive-block block*
                                      (forget meta-store x)
                                      blocks-map))])]))


(define (drive label meta-store blocks-map new-blocks) ;; -> blocks
  (let* ([block* (drive-block (blocks-map label) meta-store blocks-map)]
         [new-blocks* `(,@new-blocks(,(new-label label meta-store) . ,block*))]
         [successors (match (last block*)
                       [('return _) '()]
                       [('goto l) `(,l)]
                       [('if _ l l*) `(,l ,l*)])])
    (fold-left (lambda (blocks (label* meta-store*))
                 (if (seen-before? `(,label* ,meta-store*) blocks)
                     blocks
                     (drive label* meta-store* blocks-map blocks)))
               new-blocks*
               successors)))

(define (specialize program static-variables static-values)
  (let* ([(input-variables
           initial-label
           . blocks) program]
         [initial-meta-store (map cons static-variables static-values)]
         [dynamic-variables (difference input-variables static-variables)]
         [new-initial-label (new-label initial-label initial-meta-store)]
         [blocks-map (lambda (label) (assoc-ref blocks label))])
    `(,dynamic-variables
      ,new-initial-label
      . ,(drive initial-label initial-meta-store blocks-map '()))))


[e.g.
 (specialize example-pow '(n) '(3))
 ===>
 [(m)
  (pow ((n . 3)))

  ((pow ((n . 3))) [res := m]
                   [res := (* res m)]
                   [res := (* res m)]
                   [return res])]]
