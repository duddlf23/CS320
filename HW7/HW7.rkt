#lang plai

;; BFAE abstract syntax trees
(define-type BFAE
  [num (n number?)]
  [add  (left BFAE?) (right BFAE?)]
  [sub  (left BFAE?) (right BFAE?)]
  [id   (name symbol?)]
  [app  (ftn BFAE?) (arg BFAE?)]
  [fun  (param symbol?) (body BFAE?)]
  [newbox (val BFAE?)]
  [setbox (box-exp BFAE?) (val BFAE?)]
  [openbox (box-exp BFAE?)]
  [seqn (inst (listof BFAE?))]
  [rec (ids (listof symbol?)) (vals (listof BFAE?))]
  [get (record BFAE?) (name symbol?)]
  [sett (rec BFAE?) (name symbol?) (val BFAE?)])

 
;; dup_field : list -> list or error
;; 주어진 list 안에 중복되는 원소가 있을 경우 "duplicate fields" error를 내고, 그 외에는 원래의 list를 return한다.
(define (dup_field l)
  (cond
    [(check-duplicates l) (error 'parse "duplicate fields")]
    [else l]))

(test/exn (dup_field '(f x x y)) "duplicate fields")
(test (dup_field '()) '())
(test (dup_field '(a b c d)) '(a b c d))

;; parsing-record : function list -> list
;; ex) {record {a 10} {b 20}}을 parsing할 때 (record '(a b) '(10 20))의 형태로 되기 위해 쓰는 함수로
;; op는 first와 second로 id와 value를 각각 나눌 수 있다.
(define (parsing-record op l)
  (cond
    [(empty? l) empty]
    [else (cons (op (car l)) (parsing-record op (cdr l)))]))

(test (parsing-record first '((a 10) (b (+ 1 2)) (c (+ 3 (- 5 2))))) '(a b c))
(test (parsing-record second '((a 10) (b (+ 1 2)) (c (+ 3 (- 5 2))))) '(10 (+ 1 2) (+ 3 (- 5 2))))

; parse : sexpr -> BFAE
;; to convert s-expressions into BFAE
(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(? symbol?) (id sexp)]
    [(list 'fun (list x) b) (fun x (parse b))]
    [(list 'newbox v) (newbox (parse v))]
    [(list 'setbox b v) (setbox (parse b) (parse v))]
    [(list 'openbox b) (openbox (parse b))]
    [(cons 'seqn x) (cond
                      [(empty? x) (error 'parse "bad syntax")]
                      [else (seqn (map parse x))])]
    [(cons 'rec b) (rec (dup_field (parsing-record first b)) (map parse (parsing-record second b)))]
    [(list 'get r b) (get (parse r) b)]
    [(list 'set r x b) (sett (parse r) x (parse b))]
    [(list f x) (app (parse f) (parse x))]
    [else (error 'parse "bad syntax")]))

(test (parse '(fun (x) (+ x y))) (fun 'x (add (id 'x) (id 'y))))
(test (parse '(rec (a 10) (b (+ 1 2)))) (rec '(a b) (list (num 10) (add (num 1) (num 2)))))
(test (parse '(get (rec (r (rec (z 0)))) r)) (get (rec '(r) (list (rec '(z) (list (num 0))))) 'r))

;; BFAE-Value abstract syntax trees
(define-type BFAE-Value
  [numV (n number?)]
  [closureV (param symbol?) (body BFAE?) (ds DefrdSub?)]
  [boxV (address integer?)]
  [recV (address integer?)])

;; Store abstract syntax trees
(define-type Store
  [mtSto]
  [aSto (address integer?) (value BFAE-Value?) (rest Store?)]
  [recSto (address integer?) (ids (listof symbol?)) (vals (listof BFAE-Value?)) (rest Store?)])


;; DefrdSub abstract syntax trees
(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value BFAE-Value?) (ds DefrdSub?)])

;; Value*Store abstract syntax trees
(define-type Value*Store
  [v*s (value BFAE-Value?) (store Store?)])

; max-address : Store -> integer
; return a max-address in store
(define (max-address st)
  (type-case Store st
    [mtSto () 0]
    [aSto (n v rest)
          (max n (max-address rest))]
    [recSto (n i v rest) (max n (max-address rest))]))

(test (max-address (mtSto)) 0)

; malloc : Store -> integer
; return a free adress in store
(define (malloc st)
  (+ 1 (max-address st)))

(test (malloc (mtSto)) 1)


;; lookup : symbol DefrdSub -> BFAE-Value
;; DefrdSub 내에서 symbol을 찾아 그에 대응되는 값을 return한다.
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free identifier")]
    [aSub (x val rest)
          (if (symbol=? x name)
              val
              (lookup name rest))]))

(test (lookup 'x (aSub 'y (numV 20) (aSub 'x (numV 10) (mtSub)))) (numV 10))

;; store-lookup : integer Store -> BFAE-Value
;; Store 내에서 특정 주소의 값을 return한다.
(define (store-lookup a st)
  (type-case Store st
    [mtSto () (error 'store-lookup "unallocated")]
    [aSto (a2 v rest)
          (if (eq? a2 a)
              v
              (store-lookup a rest))]
    [recSto (a2 i v rest) (store-lookup a rest)]))

(test (store-lookup 1 (aSto 1 (numV 10) (mtSto))) (numV 10))

;; num-op : + or - BFAE BFAE -> BFAE
;; numV 2개를 더하거나 뺸 값을 다시 numV type으로 return한다.
(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op +))
(define num- (num-op -))

(test (num+ (numV 3) (numV 8)) (numV 11))
(test (num- (numV 3) (numV 8)) (numV -5))


; interp-two : BFAE BFAE DefrdSub Store
; (Value Value Store -> Value*Store)
; -> Value*Store
; interp를 두 번하는데 그 사이에 st의 변화를 인지하는 경우를 일반화한 함수
(define (interp-two expr1 expr2 ds st handle)
  (type-case Value*Store (interp expr1 ds st)
    [v*s (val1 st2)
         (type-case Value*Store (interp expr2 ds st2)
           [v*s (val2 st3)
                (handle val1 val2 st3)])]))
; test는 밑에

;; change_store : integer BFAE-Value Store -> Store
;; Store의 특정 주소에 있는 값을 val로 치환한다.
(define (change_store a val st)
  (type-case Store st
    [mtSto () (error 'change_store "unallocated")]
    [aSto (a2 v rest)
          (if (eq? a2 a)
              (aSto a val rest)
              (aSto a2 v (change_store a val rest)))]
    [recSto (a2 i v rest)
            (recSto a2 i v (change_store a val rest))]
    ))

(test (change_store 1 (numV 4) (aSto 1 (numV 2) (mtSto))) (aSto 1 (numV 4) (mtSto)))

;; int_rec : (listof BFAE) DefrdSub Store -> (list BFAE-Values Store)
;; record 형식을 store에 저장하기 위해 모든 value와 모든 value를 계산했을 때의 st를 return
(define (int_rec vals ds st)
  (cond
    [(empty? vals) (list st)]
    [else (type-case Value*Store (interp (car vals) ds st)
            [v*s (val st2)
                   (cons val (int_rec (cdr vals) ds st2))])]))

;; test는 밑에

;; find_rec : symbol integer Store -> BFAE-Value
;; record가 저장되있는 address를 받고, 그 record 안에서 symbol의 값을 찾아 return
(define (find_rec a x st)
  (type-case Store st
    [mtSto () (error 'find_rec "no such fields")]
    [aSto (a2 v rest) (find_rec a x rest)]
    [recSto (a2 i v rest)
            (if (eq? a2 a)
                (cond
                  [(empty? i) (error 'find_rec "no such fields")]
                  [else (if (eq? (car i) x)
                            (car v)
                            (find_rec a x (recSto a2 (cdr i) (cdr v) rest)))])
                        (find_rec a x rest))]))

(test (find_rec 2 'y (recSto 2 '(x y z) (list (numV 1) (numV 2) (numV 3)) (aSto 1 (numV 5) (mtSto)))) (numV 2))

;; change_rec_store : integer symbol BFAE-Value Store -> Store
;; rec_Store의 특정 주소에 있는 x의 값을 val로 치환한다.
(define (change_rec_store a x val st)
  (type-case Store st
    [mtSto () (error 'change_rec_store "no such fields")]
    [aSto (a2 v rest) (aSto a2 v (change_rec_store a x val rest))]
    [recSto (a2 i v rest)
            (if (eq? a2 a)
                (if (member x i)
                    (recSto a2 (cons x i) (cons val v) rest)
                    (error 'change_rec_store "no such fields"))
                (recSto a2 i v (change_rec_store a x val rest)))]
    ))

(test (change_rec_store 2 'y (numV 10) (recSto 2 '(x y z) (list (numV 1) (numV 2) (numV 3)) (aSto 1 (numV 5) (mtSto)))) (recSto 2 '(y x y z) (list (numV 10) (numV 1) (numV 2) (numV 3)) (aSto 1 (numV 5) (mtSto))))

;; interp : BFAE DefrdSub Store -> Value*Store
;; BFAE와 DefrdSub, Store를 이용해 Value*Store를 구한다.
(define (interp expr ds st)
  (type-case BFAE expr
    [num (n) (v*s (numV n) st)]
    [add (l r) (interp-two l r ds st (lambda (v1 v2 st1) (v*s (num+ v1 v2) st1)))]
    [sub (l r) (interp-two l r ds st (lambda (v1 v2 st1) (v*s (num- v1 v2) st1)))]
    [id (name) (v*s (lookup name ds) st)]
    [fun (x b) (v*s (closureV x b ds) st)]
    [app (f a) (interp-two f a ds st
                           (lambda (f-val a-val st1)
                             (type-case BFAE-Value f-val
                               [numV (n) (error 'interp "")]
                               [closureV (p b d) (interp b (aSub p a-val d) st1)]
                               [boxV (a) (error 'interp "")]
                               [recV (a) (error 'interp "")])))]
    [newbox (val)
            (type-case Value*Store (interp val ds st)
              [v*s (vl st1)
                   (local [(define a (malloc st1))]
                     (v*s (boxV a)
                          (aSto a vl st1)))])]
    [setbox (bx-expr val-expr)
            (interp-two bx-expr val-expr ds st
                        (lambda (bx-val val st1)
                          (type-case BFAE-Value bx-val
                            [numV (n) (error 'interp "")]
                            [closureV (p b d) (error 'interp "")]
                            [boxV (a) 
                                  (v*s val
                                       (change_store a
                                                     val
                                                     st1))]
                            [recV (a) (error 'interp "")])))]
    [openbox (bx-expr)
             (type-case Value*Store (interp bx-expr ds st)
               [v*s (bx-val st1)
                    (type-case BFAE-Value bx-val
                      [numV (n) (error 'interp "")]
                      [closureV (p b d) (error 'interp "")]
                      [boxV (a) 
                            (v*s (store-lookup a st1) st1)]
                       [recV (a) (error 'interp "")])])]
    [seqn (in) (cond
                 [(eq? (length in) 1) (interp (car in) ds st)]
                 [else (type-case Value*Store (interp (car in) ds st)
                         [v*s (v1 st2)
                              (interp (seqn (cdr in)) ds st2)])])]
    [rec (i v) (cond
                 [(= (length i) (length v)) (local [(define x (int_rec v ds st))]
                                              (local [(define a (malloc (last x)))]
                                                     (v*s (recV a) (recSto a i (drop-right x 1) (last x)))))]
                 [else (error 'interp "wrong arity")])]
    [get (r x)
         (type-case Value*Store (interp r ds st)
           [v*s (v1 st1)
                (type-case BFAE-Value v1
                  [numV (n) (error 'interp "")]
                  [closureV (p b d) (error 'interp "")]
                  [boxV (a) (error 'interp "")]
                  [recV (a) (v*s (find_rec a x st1) st1)])])]
    [sett (r x val)
         (type-case Value*Store (interp r ds st)
           [v*s (rv st1)
                (type-case Value*Store (interp val ds st1)
                  [v*s (v2 st2)
                       (type-case BFAE-Value rv
                         [numV (n) (error 'interp "")]
                         [closureV (p b d) (error 'interp "")]
                         [boxV (a) (error 'interp "")]
                         [recV (a) (v*s v2 (change_rec_store a x v2 st2))])])])]

    ))

(test (interp (add (num 4) (num 5)) (mtSub) (mtSto)) (v*s (numV 9) (mtSto)))

;; interp-expr : BFAE -> integer or symbol
;; mtSub과 mtSto를 이용해 BFAE expr를 interpret하고, 그 결과에 따라 number or symbol을 return
(define (interp-expr expr)
  (type-case Value*Store (interp expr (mtSub) (mtSto))
    [v*s (v1 st1)
         (type-case BFAE-Value v1
           [numV (n) n]
           [closureV (p b d) 'func]
           [boxV (a) 'box]
           [recV (a) 'record])]))

(test (interp-expr (parse '(newbox 3))) 'box)


(test (interp-two (num 5) (num 4) (mtSub) (mtSto) (lambda (v1 v2 st1) (v*s (num+ v1 v2) st1))) (v*s (numV 9) (mtSto)))
(test (int_rec (list (num 1) (num 2) (num 3)) (mtSub) (mtSto)) (list (numV 1) (numV 2) (numV 3) (mtSto)))
(test (interp (parse '{seqn 5}) (mtSub) (mtSto)) (v*s (numV 5) (mtSto)))

;; example
(test (interp (parse '{{fun {b}
                          {seqn
                           {setbox b 2}
                           {openbox b}}}
                         {newbox 1}})
                (mtSub)
                (mtSto))
        (v*s (numV 2)
             (aSto 1 (numV 2) (mtSto))))

 (test (interp (parse '{{fun {b}
                          {seqn
                           {setbox b {+ 2 {openbox b}}}
                           {setbox b {+ 3 {openbox b}}}
                           {setbox b {+ 4 {openbox b}}}
                           {openbox b}}}
                         {newbox 1}})
                (mtSub)
                (mtSto))
        (v*s (numV 10)
             (aSto 1 (numV 10) (mtSto))))

(test (interp (parse '{seqn 1 2})
              (mtSub)
              (mtSto))
      (v*s (numV 2) (mtSto)))

(test (interp (parse '{{fun {b} {openbox b}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 10)
           (aSto 1 (numV 10) (mtSto))))

(test (interp (parse '{{fun {b} {seqn
                                 {setbox b 12}
                                 {openbox b}}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 12)
           (aSto 1
                 (numV 12)
                 (mtSto))))

(test (interp-expr (parse '{{fun {b} {seqn
                                      {setbox b 12}
                                      {openbox b}}}
                            {newbox 10}}))
      12)

(test (interp (parse '{{fun {b} {openbox b}}
                       {seqn
                        {newbox 9}
                        {newbox 10}}})
              (mtSub)
              (mtSto))
      (v*s (numV 10)
           (aSto 2 (numV 10)
                 (aSto 1 (numV 9) (mtSto)))))

(test (interp (parse '{{{fun {b}
                             {fun {a}
                                  {openbox b}}}
                        {newbox 9}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 9)
           (aSto 2 (numV 10)
                 (aSto 1 (numV 9) (mtSto)))))
(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b 2}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
      (v*s (numV 2)
           (aSto 1 (numV 2) (mtSto))))

(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b {+ 2 (openbox b)}}
                             {setbox b {+ 3 (openbox b)}}
                             {setbox b {+ 4 (openbox b)}}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
        (v*s (numV 10)
             (aSto 1 (numV 10) (mtSto))))


(test/exn (interp (parse '{openbox x})
                  (aSub 'x (boxV 1) (mtSub))
                  (mtSto))
          "unallocated")

;; records

(test (interp-expr (parse '{{fun {r}
                                 {get r x}}
                            {rec {x 1}}}))
      1)

(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r x}}}
                            {rec {x 1}}}))
      5)
(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   {+ {get r1 b}
                                                      {seqn
                                                       {{s r1} {g r2}}
                                                       {+ {seqn
                                                           {{s r2} {g r1}}
                                                           {get r1 b}}
                                                          {get r2 b}}}}}}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {rec {a 0} {b 2}}}                ; r1
                            {rec {a 3} {b 4}}}))               ; r2
      5)

(test (interp-expr (parse '{fun {x} x}))
      'func)
(test (interp-expr (parse '{newbox 1}))
      'box)
(test (interp-expr (parse '{rec}))
      'record)

(test (interp (parse '{{fun {b} {setbox b 2}} {seqn {newbox 0} {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 2) (aSto 2 (numV 2) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{fun {b} {setbox b 2}} {newbox 0}}) (mtSub) (aSto 1 (numV 0) (mtSto))) (v*s (numV 2) (aSto 2 (numV 2) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{{fun {a} {fun {b} {setbox a 2}}} {newbox 1}} {newbox 0}}) (mtSub) (mtSto)) (v*s (numV 2) (aSto 2 (numV 0) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{+ {{fun {b} {setbox b 2}} {newbox 0}} {{fun {b} {setbox b 2}} {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 4) (aSto 2 (numV 2) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{newbox {{fun {b} {setbox b 2}} {newbox 0}}}) (mtSub) (mtSto)) (v*s (boxV 2) (aSto 2 (numV 2) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{openbox {{fun {b} {seqn {setbox b 2} {newbox {fun {a} {setbox a 3}}}}} {newbox 0}}}) (mtSub) (mtSto)) (v*s (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 2 (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{{openbox {{fun {b} {seqn {setbox b 2} {newbox {fun {a} {setbox a 3}}}}} {newbox 0}}} {newbox 1}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 3 (numV 3) (aSto 2 (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 1 (numV 2) (mtSto))))))
(test (interp (parse '{seqn {newbox 0} {setbox x 1} {openbox x}}) (aSub 'x (boxV 1) (mtSub)) (aSto 1 (numV 0) (mtSto))) (v*s (numV 1) (aSto 2 (numV 0) (aSto 1 (numV 1) (mtSto)))))
(test (interp (parse '{{fun {b} {+ {openbox b} {seqn {setbox b 2} {openbox b}}}} {newbox 1}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 1 (numV 2) (mtSto))))
(test (interp (parse '{{fun {a} {{fun {b} {seqn {setbox b {- {openbox b} 1}} {setbox a {+ {openbox a} 1}} {newbox 0} {openbox b}}} {newbox 1}}} {newbox 2}}) (aSub 'a (boxV 0) (mtSub)) (mtSto)) (v*s (numV 0) (aSto 3 (numV 0) (aSto 2 (numV 0) (aSto 1 (numV 3) (mtSto))))))
(test (interp (parse '{seqn {newbox 1}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (numV 1) (mtSto))))
(test (interp (parse '{setbox {{fun {b} {seqn {newbox b} {newbox b}}} 0} 1}) (mtSub) (mtSto)) (v*s (numV 1) (aSto 2 (numV 1) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{fun {a} {{fun {b} {seqn {setbox b 2} {setbox a {fun {c} {+ c 1}}} {{openbox a} {openbox b}}}} {openbox a}}} {newbox {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 2 (closureV 'c (add (id 'c) (num 1)) (aSub 'b (boxV 1) (aSub 'a (boxV 2) (mtSub)))) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{seqn 1 {fun {x} {+ x 1}} {newbox 2} {{fun {x} {setbox x {newbox 1}}} {newbox 3}}}) (mtSub) (mtSto)) (v*s (boxV 3) (aSto 3 (numV 1) (aSto 2 (boxV 3) (aSto 1 (numV 2) (mtSto))))))
(test (interp (parse '{{fun {b} {seqn {setbox b b} {openbox b}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (boxV 1) (mtSto))))
(test (interp (parse '{{fun {b} {openbox {setbox b b}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (boxV 1) (mtSto))))
(test (interp (parse '{{fun {b} {- {openbox b} {seqn {setbox b b} {setbox {openbox b} 1} {openbox b}}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (numV -1) (aSto 1 (numV 1) (mtSto))))
(test (interp-expr (parse '{{fun {b} {{fun {a} {seqn {set a x {openbox b}} {setbox b 1} {set a y {openbox b}} {get a x}}} {rec {x 1} {y 2}}}} {newbox 0}})) 0)
(test (interp-expr (parse '{set {rec {x 1}} x 0})) 0)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 1} {get r y}}} {{fun {b} {rec {x b} {y {openbox b}}}} {newbox 0}}})) 0)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 1} {get r y}}} {{fun {b} {rec {x b} {y {openbox b}}}} {newbox 0}}})) 0)
(test (interp-expr (parse '{{fun {r1} {{fun {r} {seqn {set r x 0} {get r1 x}}} {rec {x 1} {y 2}}}} {rec {x 3} {y 4}}})) 3)
(test (interp-expr (parse '{{fun {r} {+ {get r x} {seqn {set r x 2}}}} {rec {z 3} {y 2} {x 1}}})) 3)
(test (interp-expr (parse '{{fun {b} {seqn {set {openbox b} y {newbox {openbox b}}} {openbox {get {openbox b} y}}}} {newbox {rec {x 1} {y 2}}}})) 'record)
(test (interp-expr (parse '{{fun {b} {seqn {set {openbox b} y {newbox {openbox b}}} {get {openbox {get {openbox b} y}} y}}} {newbox {rec {x 1} {y 2}}}})) 'box)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 2)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 2)
(test (interp-expr (parse '{{fun {r} {+ {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 4)


