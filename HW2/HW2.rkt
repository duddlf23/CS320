#lang plai

(define-type WAE
  [num (n number?)]
  [add (lhs WAE?) (rhs WAE?)]
  [sub (lhs WAE?) (rhs WAE?)]
  [with (name symbol?)
        (named-expr WAE?)
        (body WAE?)]
  [id (name symbol?)])

; symbol<? symbol symbol -> boolean
; Compare the priorities of the two symbols.
(define (symbol<? a b)
  (string<? (symbol->string a)
            (symbol->string b)))


; non-sorted-free-ids: WAE -> list-of-sym
; to produces a list should contain a symbol
; for each free identifier in the wae
(define (non-sorted-free-ids wae)
  (type-case WAE wae
    [num (n) empty]
    [add (l r) (append (non-sorted-free-ids l) (non-sorted-free-ids r))]
    [sub (l r) (append (non-sorted-free-ids l) (non-sorted-free-ids r))]
    [with (bound-id named-expr bound-body) (append (non-sorted-free-ids named-expr) (remove* (list bound-id) (non-sorted-free-ids bound-body)))]
    [id (s) (list s)]))

; free-ids : WAE -> list-of-sym
; to produces a list should contain a symbol for 
; each free identifier in the wae and remove duplications and sort them
(define (free-ids wae)
  (sort (remove-duplicates (non-sorted-free-ids wae)) symbol<?))

(test (free-ids (with 'x (num 3) (add (id 'x) (sub (num 3) (id 'x))))) '())
(test (free-ids (with 'x (num 3) (sub (id 'a) (add (num 4) (id 'x))))) '(a))
(test (free-ids (with 'x (num 3) (sub (id 'b) (sub (id 'a) (id 'x))))) '(a b))
(test (free-ids (with 'x (num 3) (sub (id 'a) (sub (id 'b) (add (id 'x) (id 'b)))))) '(a b))
(test (free-ids (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'b) (id 'a))))))) '(a b y))
(test (free-ids (with 'x (id 't) (sub (id 'x) (with 'y (id 'y) (add (id 'x) (sub (id 'b) (id 'a))))))) '(a b t y))
(test (free-ids (with 'x (with 'y (num 3) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y)))) '(x y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'a) (id 'a)))) '(a b c y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(b c d y))
(test (free-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(b c d y z))



; non-sorted-binding-ids: WAE -> list-of-sym
; to produces a list should contain a symbol
; for each binding identifier in the wae
(define (non-sorted-binding-ids wae)
  (type-case WAE wae
    [num (n) empty]
    [add (l r) (append (non-sorted-binding-ids l) (non-sorted-binding-ids r))]
    [sub (l r) (append (non-sorted-binding-ids l) (non-sorted-binding-ids r))]
    [with (bound-id named-expr bound-body) (append (list bound-id) (non-sorted-binding-ids named-expr) (non-sorted-binding-ids bound-body))]
    [id (s) empty]))

; binding-ids : WAE -> list-of-sym
; to produces a list should contain a symbol for 
; each binding identifier in the wae and remove duplications and sort them
(define (binding-ids wae)
  (sort (remove-duplicates (non-sorted-binding-ids wae)) symbol<?))


(test (binding-ids (add (num 3) (sub (id 'x) (id 'y)))) '())
(test (binding-ids (with 'y (num 3) (with 'x (id 'x) (id 'y)))) '(x y))
(test (binding-ids (with 'y (num 3) (with 'y (id 'x) (add (id 'x) (id 'y))))) '(y))
(test (binding-ids (with 'y (num 3) (with 'y (with 'x (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (add (id 'x) (id 'y))))) '(x y))
(test (binding-ids (with 'z (num 3) (with 'w (with 'z (add (num 3) (id 'y)) (sub (id 'x) (id 'y))) (with 'w (id 'y) (add (num 7) (id 'w)))))) '(w z))


; non-sorted-bound-ids: WAE -> list-of-sym
; to produces a list should contain a symbol
; for each bound identifier in the wae
(define (non-sorted-bound-ids wae)
  (type-case WAE wae
    [num (n) empty]
    [add (l r) (append (non-sorted-bound-ids l) (non-sorted-bound-ids r))]
    [sub (l r) (append (non-sorted-bound-ids l) (non-sorted-bound-ids r))]
    [with (bound-id named-expr bound-body) (append (filter (lambda (x) (symbol=? x bound-id)) (free-ids bound-body)) (non-sorted-bound-ids named-expr) (non-sorted-bound-ids bound-body))]
    [id (s) empty]))

; bound-ids : WAE -> list-of-sym
; to produces a list should contain a symbol for 
; each bound identifier in the wae and remove duplications and sort them
(define (bound-ids wae)
  (sort (remove-duplicates (non-sorted-bound-ids wae)) symbol<?))

(test (bound-ids (with 'x (num 3) (add (id 'y) (num 3)))) '())
(test (bound-ids (with 'x (num 3) (add (id 'x) (sub (id 'x) (id 'y))))) '(x))
(test (bound-ids (with 'x (num 3) (add (id 'x) (with 'y (num 7) (sub (id 'x) (id 'y)))))) '(x y))
(test (bound-ids (with 'x (num 3) (with 'y (id 'x) (sub (num 3) (id 'y))))) '(x y))
(test (bound-ids (with 'x (num 3) (add (id 'y) (with 'y (id 'x) (sub (num 3) (num 7)))))) '(x))
(test (bound-ids (with 'x (id 'x) (add (id 'y) (with 'y (id 'y) (sub (num 3) (with 'z (num 7) (sub (id 'z) (id 'x)))))))) '(x z))
(test (bound-ids (with 'x (with 'y (num 3) (add (id 'x) (id 'y))) (add (id 'y) (with 'y (id 'y) (sub (num 3) (num 7)))))) '(y))
(test (bound-ids (with 'x (id 'a) (with 'y (id 'b) (with 'z (id 'c) (add (id 'd) (sub (id 'x) (add (id 'y) (id 'z)))))))) '(x y z))
(test (bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'a)))) '(a x))
(test (bound-ids (add (with 'x (num 10) (with 'x (num 3) (sub (id 'y) (with 'y (num 7) (add (id 'x) (sub (id 'c) (id 'b))))))) (with 'a (id 'd) (id 'z)))) '(x))

(test (free-ids (with 'x (with 'y (num 20) (add (id 'y) (num 3))) (with 'z (num 10) (sub (id 'x) (id 'z))))) '())
(test (binding-ids (with 'x (with 'y (num 20) (add (id 'y) (num 3))) (with 'z (num 10) (sub (id 'x) (id 'z))))) '(x y z))
(test (bound-ids (with 'x (with 'y (num 20) (add (id 'y) (num 3))) (with 'z (num 10) (sub (id 'x) (id 'x))))) '(x y))
