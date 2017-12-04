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


;(define (seen-before? label blocks) (member? label (map car blocks)))

(define ((whistle? (l* ms*)) #;with-ancestor (l ms))
  (and (equal? l l*)
       (not (equal? ms ms*)) ;; to ignore "clean instances", cf seen-before?
       #;(equal? (map car ms) (map car ms*))
       (subset? (map car ms) (map car ms*))
       (every (lambda ([k . e])
                (let ([e* (assoc-ref ms* k)])
                  (or (not e*) (homeomorphically-embedded? e e*))))
              ms)))

(define (homeomorphically-embedded? val val*)
  (match `(,val ,val*)
    [(e e) #t]
    [((? number? n) (? number? m)) (< (abs n) (abs m))]
    [((h . t) (h* . t*)) (or (and (homeomorphically-embedded? h h*)
                                  (homeomorphically-embedded? t t*))
                             (homeomorphically-embedded? val h*)
                             (homeomorphically-embedded? val t*))]
    [(e (h . t)) (or (homeomorphically-embedded? e h)
                     (homeomorphically-embedded? e t))]
    [_ #f]))

[e.g. (homeomorphically-embedded? '(w e) '(q w e))]
[e.g. (homeomorphically-embedded? '(w e) '(q (w e) a))]
[e.g. (homeomorphically-embedded? '(2 3) '(4 5))]
[e.g. (homeomorphically-embedded? 'abc 'abc)]
[e.g. (not (homeomorphically-embedded? 5 3))]
[e.g. (not (homeomorphically-embedded? '(q w e) '(w e)))]
[e.g. (not (homeomorphically-embedded? '(q w) '(x y)))]

(define (generalization #;of meta-store #;st meta-store* #;is-its-instance)
  (match meta-store
    [() '()]
    [((var . val) . meta-store)
     (let* ([val* (assoc-ref meta-store* var)])
       (if (equal? val val*)
           `((,var . ,val) . ,(generalization meta-store meta-store*))
           (generalization meta-store meta-store*)))]))

[e.g. (generalization '([m . 2] [res . 1]) '([m . 2] [res . 2]))
      ===> ([m . 2])]


(define (generalizing-block label meta-store meta-store*)
  (let* ([new-meta-store (generalization meta-store meta-store*)]
         [forgetting-vars (difference (map car meta-store)
                                      (map car new-meta-store))]
         [assignments (map (lambda (v) `[,v := ,(assoc-ref meta-store v)])
                           forgetting-vars)])         
    `(,(new-label label meta-store)
      . (,@assignments [goto ,(new-label label new-meta-store)]))))

[e.g. (generalizing-block 'test '([m . 2] [res . 1]) '([m . 2] [res . 2]))
      ===> ((test ([m . 2] [res . 1])) [res := 1]
                                       [goto (test ([m . 2]))])]


(define (co-tail xs)
  (match xs
    [(_) '()]
    [(x . xs) `(,x . ,(co-tail xs))]))

(define (drive label meta-store blocks-map ancestors)
;  (pretty-print `(DRAJW ,label ,meta-store))
  (if (member? (new-label label meta-store) ancestors)
      '()
      (let* ([label* (new-label label meta-store)]
             [block* 
              (match (find (whistle? label*) ancestors)
                [(_ ms*) (let ([(_ . block*) (generalizing-block label
                                                                 meta-store
                                                                 ms*)])
                           block*)]
                [#f (drive-block (blocks-map label) meta-store blocks-map)])]
             ;[_elo_ (pretty-print `[BLCK ,block*])]             
             [ancestors* `(,label* . ,ancestors)])
        (match (last block*)
          [['return _]
           `([,label* . ,block*])]

          [['goto (l ms)]
           (match (drive l ms blocks-map ancestors*)
             [('GENERALZE (l ms) (l* ms*))
              (if (and (equal? l label)
                       (equal? ms meta-store))
                  (drive label (generalization ms ms*) blocks-map ancestors)
                  `(GENERALIZE (,l ,ms) (,l* ,ms*)))]
             [([label-n . block-n] . rest-n)
              `([,label* . ,block*] [,label-n . ,block-n] . ,rest-n)])]

          [['if e (l ms) (l* ms*)]
           (match (drive l ms blocks-map ancestors*)
             [('GENERALIZE (l ms) (l* ms*))
              (if (and (equal? l label)
                       (equal? ms meta-store))
                  (let ([(((_ . ms-gen) . block-gen) . rest-gen)
                         (drive label (generalization ms ms*)
                                blocks-map ancestors)])
                    `([,(new-label label ms-gen) . block-gen]
                      . ,rest-gen))
                  `(GENERALIZE (,l ,ms) (,l* ,ms*)))]
             [()
              (match (drive l* ms* blocks-map ancestors*)
                [('GENERALIZE (l ms) (l* ms*))
                 (if (and (equal? l label)
                          (equal? ms meta-store))
                     (drive label (generalization ms ms*) blocks-map ancestors)
                     `(GENERALIZE (,l ,ms) (,l* ,ms*)))]
                [()
                 '()]
                [([label-e . block-e] . rest-e)                 
                 `([,label* . (,@(co-tail block*)
                               [if ,e ,(new-label l* ms*) ,label-e])]
                   [,label-e . ,block-e]
                   . ,rest-e)])]

             [([label-t . block-t] . rest-t)
              (match (drive l* ms* blocks-map ancestors*)
                [('GENERALIZE (l ms) (l* ms*))
                 (if (and (equal? l label)
                          (equal? ms meta-store))
                     (drive label (generalization ms ms*) blocks-map ancestors)
                     `(GENERALIZE (,l ,ms) (,l* ,ms*)))]
                [()
                 `([,label* . (,@(co-tail block*)
                               [if ,e ,label-t ,(new-label l* ms*)])]
                   [,label-t . ,block-t]
                   ,@rest-t)]
                [([label-e . block-e] . rest-e)
                 `([,label* . (,@(co-tail block*)
                               [if ,e ,label-t ,label-e])]
                   [,label-t . ,block-t]
                   ,@rest-t
                   [,label-e . ,block-e]
                   ,@rest-e)]
                [wtf (pretty-print `(WTTFFF? ,wtf))] )]
             [wtf (pretty-print `(wtf ,wtf))])]))))


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
      . ,(delete-duplicates
          (drive initial-label initial-meta-store blocks-map '())))))


;;; ha! ;; -------------------------------------------------------
[e.g. (specialize example-pow '(n) '(3))
      ===> ((m)
            (pow ((n . 3)))

            ((pow ((n . 3))) (res := m)
                             (res := (* res m))
                             (res := (* res m))
                             (return res)))]

;; -------------------------------------------------------
[e.g. (specialize example-pow '(m) '(3))
      ===> ((n)
            (pow ((m . 3)))

            ((pow ((m . 3))) [if (= n 0)
                                 (end ((m . 3) (res . 1)))
                                 (loop ((m . 3) (res . 1)))])
            ((end ((m . 3) (res . 1))) [return 1])
            ((loop ((m . 3) (res . 1))) [n := (- n 1)]
                                        [if (= n 0)
                                            (end ((m . 3) (res . 3)))
                                            (loop ((m . 3) (res . 3)))])
            ((end ((m . 3) (res . 3))) [return 3])
            ((loop ((m . 3) (res . 3))) [res := 3]
                                        [goto (loop ((m . 3)))])
            ((loop ((m . 3))) [res := (* res 3)]
                              [n := (- n 1)]
                              [if (= n 0) (end ((m . 3))) (loop ((m . 3)))])
            ((end ((m . 3))) [return res]))]

;; -------------------------------------------------------
[e.g. (specialize example-pow '() '())
      ===> ((m n)
            (pow ())

            ((pow ()) [if (= n 0) (end ((res . 1))) (loop ((res . 1)))])
            ((end ((res . 1))) [return 1])
            ((loop ((res . 1))) [res := m]
                                [n := (- n 1)]
                                [if (= n 0) (end ()) (loop ())])
            ((end ()) [return res])
            ((loop ()) [res := (* res m)]
                       [n := (- n 1)]
                       [if (= n 0) (end ()) (loop ())]))]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define example-apd
  '((xs ys)
    apd
    (apd [res := ys]
         [goto test])
    (test [if (= xs ()) end loop])
    (loop [res := (cons (car xs) res)]
          [xs := (cdr xs)]
          [goto test])
    (end [return res])))

[e.g. (specialize example-apd '(xs) '((q w e)))
      ===> ((ys)
            (apd ((xs q w e)))

            ((apd ((xs q w e))) [res := ys]
                                [res := (cons 'q res)]
                                [res := (cons 'w res)]
                                [res := (cons 'e res)]
                                [return res]))]
;; -------------------------------------------------------
[e.g. (specialize example-apd '(ys) '((q w e)))
      ===> ((xs)
            (apd ((ys q w e)))

            ((apd ((ys q w e))) [if (= xs ())
                                    (end ((ys q w e) (res q w e)))
                                    (loop ((ys q w e) (res q w e)))])
            ((end ((ys q w e) (res q w e))) [return '(q w e)])
            ((loop ((ys q w e) (res q w e))) [res := (cons (car xs) '(q w e))]
                                             [xs := (cdr xs)]
                                             [if (= xs ())
                                                 (end ((ys q w e)))
                                                 (loop ((ys q w e)))])
            ((end ((ys q w e))) [return res])
            ((loop ((ys q w e))) [res := (cons (car xs) res)]
                                 [xs := (cdr xs)]
                                 [if (= xs ())
                                     (end ((ys q w e)))
                                     (loop ((ys q w e)))]))]
;; -------------------------------------------------------
[e.g. (specialize example-apd '() '())
      ===> ((xs ys)
            (apd ())

            ((apd ()) [res := ys]
                      [if (= xs ()) (end ()) (loop ())])
            ((end ()) [return res])
            ((loop ()) [res := (cons (car xs) res)]
                       [xs := (cdr xs)]
                       [if (= xs ()) (end ()) (loop ())]))]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

[e.g. (specialize example-stck '(formula inputs) '((DUP * SWAP DUP * +) (3 4)))
      ===> (()
            (init ((formula DUP * SWAP DUP * +) (inputs 3 4)))
            ((init ((formula DUP * SWAP DUP * +) (inputs 3 4))) [return 25]))]
;; ----------------------------------------------
;;; BOOM Ist Futamura projection:
[e.g. (specialize example-stck '(formula) '((DUP * SWAP DUP * +)))
      ===> ((inputs)
            (init ((formula DUP * SWAP DUP * +)))

            ((init ((formula DUP * SWAP DUP * +))) [stck := inputs]
                                                   [a := (car stck)]
                                                   [stck := (cons a stck)]
                                                   [a := (car stck)]
                                                   [stck := (cdr stck)]
                                                   [b := (car stck)]
                                                   [stck := (cdr stck)]
                                                   [stck := (cons (* b a) stck)]
                                                   [a := (car stck)]
                                                   [stck := (cdr stck)]
                                                   [b := (car stck)]
                                                   [stck := (cdr stck)]
                                                   [stck := (cons b (cons a stck))]
                                                   [a := (car stck)]
                                                   [stck := (cons a stck)]
                                                   [a := (car stck)]
                                                   [stck := (cdr stck)]
                                                   [b := (car stck)]
                                                   [stck := (cdr stck)]
                                                   [stck := (cons (* b a) stck)]
                                                   [a := (car stck)]
                                                   [stck := (cdr stck)]
                                                   [b := (car stck)]
                                                   [stck := (cdr stck)]
                                                   [stck := (cons (+ b a) stck)]
                                                   [return (car stck)]))]
;;; how cool is that?
;; ----------------------------------------------
;;; plus no visible overhead /neither gain ofc/:
[e.g. (specialize example-stck '() '())
      ===> ((formula inputs)
            (init ())

            ((init ()) [stck := inputs]
                       [cmd := (car formula)]
                       [cnt := (cdr formula)]
                       [if (= cmd '+) (add ()) (test-cmd* ())])
            ((add ()) [a := (car stck)]
                      [stck := (cdr stck)]
                      [b := (car stck)]
                      [stck := (cdr stck)]
                      [stck := (cons (+ b a) stck)]
                      [if (= cnt ()) (halt ()) (step ())])
            ((halt ()) [return (car stck)])
            ((step ()) [cmd := (car cnt)]
                       [cnt := (cdr cnt)]
                       [if (= cmd '+) (test-cmd* ()) (test-cmd* ())])
            ((test-cmd* ()) [if (= cmd '*) (mul ()) (test-cmd** ())])
            ((mul ()) [a := (car stck)]
                      [stck := (cdr stck)]
                      [b := (car stck)]
                      [stck := (cdr stck)]
                      [stck := (cons (* b a) stck)]
                      [if (= cnt ()) (halt ()) (step ())])
            ((test-cmd** ()) [if (= cmd '-) (sub ()) (test-cmd*** ())])
            ((sub ()) [a := (car stck)]
                      [stck := (cdr stck)]
                      [b := (car stck)]
                      [stck := (cdr stck)]
                      [stck := (cons (- b a) stck)]
                      [if (= cnt ()) (halt ()) (step ())])
            ((test-cmd*** ()) [if (= cmd 'DUP) (dup ()) (test-cmd**** ())])
            ((dup ()) [a := (car stck)]
                      [stck := (cons a stck)]
                      [if (= cnt ()) (halt ()) (step ())])
            ((test-cmd**** ()) [if (= cmd 'SWAP) (swap ()) (error ())])
            ((swap ()) [a := (car stck)]
                       [stck := (cdr stck)]
                       [b := (car stck)]
                       [stck := (cdr stck)]
                       [stck := (cons b (cons a stck))]
                       [if (= cnt ()) (halt ()) (step ())])
            ((error ()) [return 'ERROR])
            ((step ()) [cmd := (car cnt)]
                       [cnt := (cdr cnt)]
                       [if (= cmd '+) (add ()) (test-cmd* ())]))]

;;; NICE.
