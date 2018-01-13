#lang racket
(provide fail)
(provide succeed)
(provide var)
(provide ==)
(provide any)
(provide empty-s)
(provide all)
(provide one)
(provide fresh)
(provide reify)
(provide run*)
(provide _)
(provide conso)
(provide caro)
(provide cdro)
(provide memo)
(provide lefto)
(provide nexto)
(provide ntheqo)
(provide ntho)
(provide pairo)
(provide nullo)
(provide eqo)
(provide all-uniqueo)
(provide neg)
(provide caro-therefore-all-not-cdro)

; Failed goal
(define fail
  (lambda (x)
    '()))

; Succeed goal
(define succeed
  (lambda (x)
    (list x)))

; Define a variable
(define var
  (lambda (x)
    (cons '? x)))

; Check if a parameter is a variable
(define var?
  (lambda (x)
    (and (pair? x)
         (eq? (car x) '?))))

; Total ignorance
(define empty-s '())

; Adds the association of the variable x with the value v to the substiution s
(define ext-s
  (lambda (x v s)
    (cons (cons x v) s)))

; Looks up the value x in the substitution s
; (walk vx (list (list vx 'bread))) => 'bread
; (walk vx (list (list vx vy) (list vz 'sushi) (list vy vz))) => 'sushi
(define walk
  (lambda (x s)
    (cond ((not (var? x)) x)
          (else
           (let ((v (assq x s)))
             (cond (v (walk (cdr v) s))
                   (else x)))))))

; Everything not a pair is an atom
(define atom?
  (lambda (x)
    (not (pair? x))))

; Unify x with y
(define unify
  (lambda (x y s)
    (let ((x (walk x s))
          (y (walk y s)))
      (cond
        ((eqv? x y) s)
        ((var? x) (ext-s x y s))
        ((var? y) (ext-s y x s))
        ((or (atom? x)
             (atom? y)) #f)
        (else (let ((s (unify (car x) (car y) s)))
                (and s (unify (cdr x) (cdr y) s))))))))

; Like unify but is a goal
; (== vq 'orange-juice) => #<procedure:...
; ((== vq 'orange-juice) '()) => '((((? . vq) . orange-juice)))
(define (== x y)
  (lambda (s)
    (let ((s2 (unify x y s)))
      (cond (s2 (succeed s2))
            (else (fail s))))))

; Applies each member of the list of goals g* to the given knowledge
; s and appends the results
; ((any* (== vq 'ice) (== vq 'cream)) empty-s) => '((((? . vq) . ice)) (((? . vq) . cream)))
(define (any* . g*)
  (lambda (s)
    (letrec
        ((try
          (lambda g*
            (cond ((null? g*) (fail s))
                  (else (append ((car g*) s)
                                (apply try (cdr g*))))))))
      (apply try g*))))

; Applies each member of the list of goals g* to the given knowledge
; s and appends the results
; ((any* (== vq 'ice) (== vq 'cream)) empty-s) => '((((? . vq) . ice)) (((? . vq) . cream)))
; ((== vq (list vq)) empty-s) => '((((? . vq) (? . vq))))
(define-syntax any
  (syntax-rules ()
    ((_) fail)
    ((_ g ...)
     (any*
      (lambda (s)
        (g s))
      ...))))

; Applies all it's subgoals to the knowledge s*
(define (all . g*)
  (lambda (s)
    (letrec
        ((try
          (lambda (g* s*)
            (cond ((null? g*) s*)
                  (else (try (cdr g*)
                             (apply append
                                    (map (car g*) s*))))))))
      (try g* (succeed s)))))

; Failed check
(define failed? null?)

; Returns s as soon as its subgoal succeeds
(define (one* . g*)
  (lambda (s)
    (letrec
        ((try
          (lambda (g*)
            (cond ((null? g*) (fail s))
                  (else (let ((out ((car g*) s)))
                          (cond ((failed? out) (apply try (cdr g*)))
                                (else out))))))))
      (apply try g*))))

; Returns s as soon as its subgoal succeeds with eta expansion
(define-syntax one
  (syntax-rules ()
    ((_) fail)
    ((_ g ...)
     (one*  (lambda (s) (g s)) ...))))

; Negation
(define neg
  (lambda (g)
    (lambda (s)
      (let ((out (g s)))
        (cond ((failed? out) (succeed s))
              (else (fail s)))))))

; Create fresh variables
; (fresh (a b c) (list a b c)) => '((? . a) (? . b) (? . c))
(define-syntax fresh
  (syntax-rules ()
    ((_ () g)
     (let () g))
    ((_ (v ...) g)
     (let ((v (var 'v)) ...) g))))

; Checks whether the symbol or variable x occurs in the form y
(define occurs?
  (lambda (x y s)
    (let ((v (walk y s)))
      (cond
        ((var? y) (eq? x y))
        ((var? v) (eq? x v))
        ((atom? v) #f)
        (else (or (occurs? x (car v) s)
                  (occurs? x (cdr v) s)))))))

; Checks if the value of a variable is cirular
(define circular?
  (lambda (x s)
    (let ((v (walk x s)))
      (and (not (eq? x v))
           (occurs? x (walk x s) s)))))

; failure value
(define *failure* (var 'failure))

; Brings the answers generated into a comprehensible form
; (walk* vq (list (list vx 'foo) (list vq (list vx)))) => '(foo)
(define walk*
  (lambda (x s)
    (letrec ((w* (lambda (x s)
                   (let ((x (walk x s)))
                     (cond
                       ((var? x) x)
                       ((atom? x) x)
                       (else (cons (w* (car x) s)
                                   (w* (cdr x) s))))))))
      (cond ((circular? x s) *failure*)
            ((eq? x (walk x s)) empty-s)
            (else (w* x s))))))

; Generate a reified name
(define reify-name
  (lambda (n)
    (string->symbol
     (string-append "_." (number->string n)))))

; Creates a substitution in which each fresh variable contained
; in the form v is associated with a unique reified name
(define reify
  (lambda (v)
    (letrec ((reify-s
              (lambda (v s)
                (let ((v (walk v s)))
                  (cond ((var? v)
                         (ext-s v (reify-name (length s)) s))
                        ((atom? v) s)
                        (else (reify-s (cdr v)
                                       (reify-s (car v)
                                                s))))))))
      (reify-s v empty-s))))

; Turns a result into () when there is a circular value in it
(define propagate-failure
  (lambda (s)
    (cond ((occurs? *failure* s s) '())
          (else s))))

; Processes a query
(define query
  (lambda (x g)
    (propagate-failure
     (map (lambda (s)
            (walk* x (append s (reify (walk* x s)))))
          (g empty-s)))))

; Runs goal
(define-syntax run*
  (syntax-rules ()
    ((_ () goal) (query #f goal))
    ((_ (v) goal) (query v goal))))

; blank var
(define (_) (var '_))

; conso the magnificent
; (run* (vq) (conso 'heads vq '(heads tails))) => '((tails))
; (run* (vq) (conso vq '(tails) '(heads tails))) => '(heads)
(define conso
  (lambda (a d p)
    (== (cons a d) p)))

; Returns first element of a list
; (run* (vq) (caro '(x y) vq)) => '(x)
(define caro
  (lambda (p a)
    (fresh (_)
           (conso a _ p))))

; Returns everything after the first element of a list
; (run* (vq) (cdro '(x y) vq)) => '((y))
(define cdro
  (lambda (p d)
    (fresh (_)
           (conso _ d p))))

; Says if a value is a member of a list
; (run* () (memo 'c '(a b c d e f))) => '(())
; (run* () (memo 'x '(a b c d e f))) => '()
(define memo
  (lambda (x l)
    (fresh (a d)
           (any (all (caro l a)
                     (== x a))
                (all (cdro l d)
                     (memo x d))))))

; Checks if x is to the left of y in a list
(define lefto
  (lambda (x y l)
    (fresh (h t ht)
           (any (all (caro l h)
                     (cdro l t)
                     (caro t ht)
                     (== h x)
                     (== ht y))
                (all (cdro l t)
                     (lefto x y t))))))

; x is next to y if x is on the left of y or y on the left of x
(define nexto
  (lambda (x y l)
    (any (lefto x y l)
         (lefto y x l))))

; Succeeds if x matches the nth element in l
; (fresh (h) (run* (h) (ntheqo 1  'b '(a b c d)))) => '(())
; (fresh (h) (run* (h) (ntheqo 1  'b '(a b c d)))) => '()
(define ntheqo
  (lambda (n x l)
    (fresh (h)
           (cond ((= n 0)
                  (all 
                   (caro l h)
                   (== h x)))
                 (else
                  (all
                   (cdro l h)
                   (ntheqo (- n 1) x h)))))))            

; Select the nth element
; (fresh (h) (run* (h) (ntho 1 '(a b c d) h)))
; (fresh (h) (run* (h) (ntho 2 '(a b c d) h)))
(define ntho
  (lambda (n l a)
    (fresh (h)
           (cond ((= n 0)
                  (caro l a))
                 (else
                  (all 
                   (cdro l h)
                   (ntho (- n 1) h a)))))))

; Unify as a pair
(define pairo
  (lambda (p)
    (fresh (a d)
           (conso a d p))))

; Check if null
; (fresh (x) (run* (x) (nullo x))) => '(())
; (fresh (x) (run* (x) (all (== x 'a) (nullo x)))) => '()
(define nullo
  (lambda (x)
    (== '() x)))

; Unify with ==
(define eqo
  (lambda (x y)
    (== x y)))

; Succeeds with a list of unique values
(define all-uniqueo
  (lambda (l h)
    (letrec ((all-unique-helpero
              (lambda (l lol acc h)
                (fresh (a b c)
                       (any (all (nullo lol)
                                 (== h acc))
                            (all (caro lol a)
                                 (cdro lol b)
                                 (eqo l a)
                                 (all-unique-helpero l b acc h))
                            (all (caro lol a)
                                 (cdro lol b)
                                 (neg (eqo l a))
                                 (conso a acc c)
                                 (all-unique-helpero l b c h)))))))
      (fresh (a b c d)
             (any (nullo l)  
                  (all (caro l a)
                       (cdro l b)
                       (all-unique-helpero a b '() c)
                       (all-uniqueo c d)
                       (any (all (nullo d)
                                 (== (list a) h))
                            (all (neg (nullo d))
                                 (conso a d h)))))))))

; Car is true therefore all of cdr is false
; alternatively, first element in list is false so at least one of cdr it true
(define caro-therefore-all-not-cdro
  (lambda (lst h)
    (letrec ((check
              (lambda (lst h)
                (fresh (a b)
                       (all (caro lst a)
                            (cdro lst b)
                            (any (memo a h)
                                 (check b h))))))
             (neg-check
              (lambda (lst h)
                (fresh (a b)
                       (all (caro lst a)
                            (cdro lst b)
                            (all (memo a h)
                                 (neg (check b h))))))))
    (fresh (a b)
           (all (caro lst a)
                (cdro lst b)
                (any (all (memo a h)
                          (neg-check (memo b h)))
                     (all (neg (memo a h))
                          (check b h))))))))
