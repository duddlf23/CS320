#lang plai

(require (for-syntax racket/base) racket/match racket/list racket/string
         (only-in mzlib/string read-from-string-all))

;; build a regexp that matches restricted character expressions, can use only
;; {}s for lists, and limited strings that use '...' (normal racket escapes
;; like \n, and '' for a single ')
(define good-char "(?:[ \t\r\na-zA-Z0-9_{}!?*/<=>:+-]|[.][.][.])")
;; this would make it awkward for students to use \" for strings
;; (define good-string "\"[^\"\\]*(?:\\\\.[^\"\\]*)*\"")
(define good-string "[^\"\\']*(?:''[^\"\\']*)*")
(define expr-re
  (regexp (string-append "^"
                         good-char"*"
                         "(?:'"good-string"'"good-char"*)*"
                         "$")))
(define string-re
  (regexp (string-append "'("good-string")'")))

(define (string->sexpr str)
  (unless (string? str)
    (error 'string->sexpr "expects argument of type <string>"))
    (unless (regexp-match expr-re str)
      (error 'string->sexpr "syntax error (bad contents)"))
    (let ([sexprs (read-from-string-all
                 (regexp-replace*
                  "''" (regexp-replace* string-re str "\"\\1\"") "'"))])
    (if (= 1 (length sexprs))
      (car sexprs)
      (error 'string->sexpr "bad syntax (multiple expressions)"))))

(test/exn (string->sexpr 1) "expects argument of type <string>")
(test/exn (string->sexpr ".") "syntax error (bad contents)")
(test/exn (string->sexpr "{} {}") "bad syntax (multiple expressions)")

;; FWAE abstract syntax trees
(define-type FWAE
  [num (n number?)]
  [add  (left FWAE?) (right FWAE?)]
  [sub  (left FWAE?) (right FWAE?)]
  [with (name symbol?) (init FWAE?) (body FWAE?)]
  [id   (name symbol?)]
  [app  (ftn FWAE?) (arg (listof FWAE?))]
  [fun  (param (listof symbol?)) (body FWAE?)]
  [record (ids (listof symbol?)) (vals (listof FWAE?))]
  [getField (rec FWAE?) (name symbol?)])


;; dup_arg : list -> list or error
;; 주어진 list 안에 중복되는 원소가 있을 경우 "bad syntax" error를 내고, 그 외에는 원래의 list를 return한다.
(define (dup_arg l)
  (cond
    [(check-duplicates l) (error 'parse "bad syntax")]
    [else l]))

(test/exn (dup_arg '(f x x)) "bad syntax")
(test (dup_arg '()) '())
(test (dup_arg (list 1 2 3 4)) (list 1 2 3 4))
  

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
    [else (cons (op (first l)) (parsing-record op (rest l)))]))

(test (parsing-record first '((a 10) (b (+ 1 2)) (c (+ 3 (- 5 2))))) '(a b c))
(test (parsing-record second '((a 10) (b (+ 1 2)) (c (+ 3 (- 5 2))))) '(10 (+ 1 2) (+ 3 (- 5 2))))

; parse-sexpr : sexpr -> FWAE
;; to convert s-expressions into FWAE
(define (parse-sexpr sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r) (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'with (list x i) b) (cond
                                 [(or (symbol=? x '+) (symbol=? x '-) (symbol=? x 'with) (symbol=? x 'fun)) (error 'parse "bad syntax")]
                                 [else (with x (parse-sexpr i) (parse-sexpr b))])]
    [(? symbol?) (cond
                   [(or (symbol=? sexp '+) (symbol=? sexp '-) (symbol=? sexp 'with) (symbol=? sexp 'fun)) (error 'parse "bad syntax")]
                   [else (id sexp)])]
    [(list 'fun args b) (fun (dup_arg args) (parse-sexpr b))]
    [(list 'getField r b) (getField (parse-sexpr r) b)]
    [(cons a b) (cond
                  [(eq? a 'record) (cond
                                     [(or (member '+ (parsing-record first b)) (member '- (parsing-record first b)) (member 'with (parsing-record first b)) (member 'fun (parsing-record first b))) (error 'parse "bad syntax")]
                                     [else (record (dup_field (parsing-record first b)) (map parse-sexpr (parsing-record second b)))])]
                  [else (app (parse-sexpr a) (map parse-sexpr (rest sexp)))])]
    [else (error 'parse "bad syntax")]))

(test (parse-sexpr '(fun (x y) (+ x y))) (fun '(x y) (add (id 'x) (id 'y))))
(test/exn (parse-sexpr '(record (+ 3) (a 3))) "bad syntax")

;; parses a string containing a FWAE expression to a FWAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

(test (parse "{record {a 10} {b {+ 1 2}}}") (record '(a b) (list (num 10) (add (num 1) (num 2)))))
(test (parse "{getField {record {r {record {z 0}}}} r}") (getField (record '(r) (list (record '(z) (list (num 0))))) 'r))

;; FWAE-Value abstract syntax trees
(define-type FWAE-Value
  [numV (n number?)]
  [closureV (param (listof symbol?)) (body FWAE?) (ds DefrdSub?)]
  [recV (ds DefrdSub?)])

;; DefrdSub abstract syntax trees
(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value FWAE-Value?) (ds DefrdSub?)])

;; lookup : symbol DefrdSub -> FWAE-Value
;; DefrdSub 내에서 symbol을 찾아 그 값을 FWAE-Value로 return한다. (record 밖에서 id를 찾을 때)
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free identifier")]
    [aSub (x val rest)
          (if (symbol=? x name)
              val
              (lookup name rest))]))
(test (lookup 'x (aSub 'y (numV 20) (aSub 'x (numV 10) (mtSub)))) (numV 10))

;; lookup2 : symbol DefrdSub -> FWAE-Value
;; DefrdSub 내에서 symbol을 찾아 그 값을 FWAE-Value로 return한다. (record 내에서 찾을 때)
(define (lookup2 name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup2 "no such field")]
    [aSub (x val rest)
          (if (symbol=? x name)
              val
              (lookup2 name rest))]))
(test/exn (lookup2 'x (aSub 'y (numV 20) (aSub 'z (numV 10) (mtSub)))) "no such field")

;; num-op : + or - FWAE FWAE -> FWAE
;; numV 2개를 더하거나 뺸 값을 다시 numV type으로 return한다.
(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op +))
(define num- (num-op -))

(test (num+ (numV 3) (numV 8)) (numV 11))
(test (num- (numV 3) (numV 8)) (numV -5))




;; interp : FWAE DefrdSub -> FWAE-Value
;; FWAE와 DefrdSub를 이용해 FWAE-Value를 구한다.
(define (interp fwae ds)
  (type-case FWAE fwae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [with (x i b) (interp b (aSub x (interp i ds) ds))]
    [id (name) (lookup name ds)]
    [fun (x b) (closureV x b ds)]
    [app (f a) (local [(define f-val (interp f ds))]
                 (type-case FWAE-Value f-val
                   [numV (n) (error 'interp "")]
                   [closureV (p b d) (interp b (sub_arg2par p a ds d))]
                   [recV (d) (error 'interp "")]))]
    [record (i v) (recV (sub_arg2par i v ds (mtSub)))]
    [getField (r x) (lookup2 x (recV-ds (interp r ds)))]))

(test (interp (add (num 4) (num 5)) (mtSub)) (numV 9))

;; sub_arg2par : (listof symbol) (listof Fwae) DefrdSub DefrdSub -> DefrdSub
;; 함수의 parameter에 dss를 기반으로 계산한 argument 값을 대입한 후 base를 토대로 DefrdSub을 갱신한다.
(define (sub_arg2par par arg ds base)
  (cond
    [(= (length par) (length arg)) (cond
                                     [(empty? par) base]
                                     [else (aSub (first par) (interp (first arg) ds) (sub_arg2par (rest par) (rest arg) ds base))])]
    [else (error 'interp "wrong arity")]))

(test (sub_arg2par '(x y) (list (num 5) (num 4)) (mtSub) (mtSub)) (aSub 'x (numV 5) (aSub 'y (numV 4) (mtSub))))
(test (sub_arg2par '(x y) (list (num 5) (add (id 'x) (num 4))) (aSub 'x (numV 6) (mtSub)) (mtSub)) (aSub 'x (numV 5) (aSub 'y (numV 10) (mtSub))))

; run : string -> number or 'function or 'record
;; interpret a FWAE program contained in a string
(define (run str)
  (type-case FWAE-Value (interp (parse str) (mtSub))
    [numV (n) n]
    [closureV (p b d) 'function]
    [recV (d) 'record]))

(test (run "{with {x 3} {with {y 5} {getField {record {a x} {b y}} a}}}") 3)
(test/exn (run "{1 2 3}") "")
(test/exn (run "{with {+ {fun {x y} {- x y}}} {+ 3 2}}") "bad syntax")

;; tests
(test (run "{record {a 10} {b {+ 1 2}}}")
      'record)
(test (run "{getField {record {a 10} {b {+ 1 2}}} b}")
      3)
(test/exn (run "{getField {record {b 10} {b {+ 1 2}}} b}")
          "duplicate fields")
(test/exn (run "{getField {record {a 10}} b}")
          "no such field")
(test (run "{with {g {fun {r} {getField r c}}}
                  {g {record {a 0} {c 12} {b 7}}}}")
      12)
(test (run "{getField {record {r {record {z 0}}}} r}")
      'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}")
      0)
(test/exn (run "{record {z {getField {record {z 0}} y}}}")
          "no such field")
(test (run "{with {f {fun {a b} {+ a b}}}
                  {with {g {fun {x} {- x 5}}}
                        {with {x {f 2 5}} {g x}}}}") 2)
(test (run "{with {f {fun {x y} {+ x y}}} {f 1 2}}") 3)
(test (run "{with {f {fun {} 5}}
                  {+ {f} {f}}}") 10)
(test (run "{with {h {fun {x y z w} {+ x w}}}
                  {h 1 4 5 6}}") 7) 
(test (run "{with {f {fun {} 4}}
                  {with {g {fun {x} {+ x x}}}
                        {with {x 10} {- {+ x {f}} {g 4}}}}}") 6)
(test (run "{record {a 10} {b {+ 1 2}}}") 'record)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)
(test (run "{with {x 3} {with {y 5} {getField {record {a x} {b y}} a}}}") 3)
(test (run "{with {f {fun {a b} {+ {getField a a} b}}}
                  {with {g {fun {x} {+ 5 x}}}
                        {with {x {f {record {a 10} {b 5}} 2}} {g x}}}}") 17)
(test (run "{with {f {fun {a b c d e} {record {a a} {b b} {c c} {d d} {e e}}}}
                  {getField {f 1 2 3 4 5} c}}") 3)
(test (run "{with {f {fun {a b c} {record {a a} {b b} {c c}}}}
                  {getField {f 1 2 3} b}}") 2)
(test (run "{with {f {fun {a b c} {record {x a} {y b} {z c} {d 2} {e 3}}}}
                  {getField {f 1 2 3} y}}") 2)
(test (run "{with {f {fun {a b c} {record {x a} {y b} {z c} {d 2} {e 3}}}}
                  {getField {f 1 2 3} d}}") 2)
(test (run "{with {f {fun {x} {+ 5 x}}}
                  {f {getField {getField {record {a {record {a 10} {b {- 5 2}}}} {b {getField {record {x 50}} x}}} a} b}}}") 8)
(test (run "{getField {record {a 10} {b {+ 1 2}}} b}") 3)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)
(test (run "{record {a 10}}") 'record)
(test (run "{getField {record {a 10}} a}") 10)
(test (run "{getField {record {a {+ 1 2}}} a}") 3)
(test (run "{fun {x} x}") 'function)
(test (run "{getField {record {a {record {b 10}}}} a}") 'record)
(test (run "{getField {getField {record {a {record {a 10}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} b}") 20)
(test (run "{+ {getField {record {a 10}} a} {getField {record {a 20}} a}}") 30)
(test (run "{+ {getField {record {a 10}} a} {getField {record {a 20}} a}}") 30)
(test (run "{record {a 10}}") 'record)
(test (run "{record {a {- 2 1}}}") 'record)
(test (run "{getField {record {a 10}} a}") 10)
(test (run "{getField {record {a {- 2 1}}} a}") 1)
(test (run "{getField {record {a {record {b 10}}}} a}") 'record)
(test (run "{getField {getField {record {a {record {a 10}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} a}") 10)
(test (run "{getField {getField {record {a {record {a 10} {b 20}}}} a} b}") 20)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)
(test (run "{with {y {record {x 1} {y 2} {z 3}}} {getField y y}}") 2)
(test (run "{with {y {record {x 1} {y 2} {z 3}}} {getField y z}}") 3)
(test (run "{record {a 10} {b {+ 1 2}}}") 'record)
(test (run "{getField {record {a 10} {b {+ 1 2}}} b}") 3)
(test (run "{with {g {fun {r} {getField r c}}}
                  {g {record {a 0} {c 12} {b 7}}}}") 12)
(test (run "{getField {record {r {record {z 0}}}} r}") 'record)
(test (run "{getField {getField {record {r {record {z 0}}}} r} z}") 0)