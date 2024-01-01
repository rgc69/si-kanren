;(push '*default-pathname-defaults* asdf:*central-registry*)
;(asdf:load-system :si-kanren)

(defpackage :si-kanren
    (:use :common-lisp))

(in-package :si-kanren)

(defun pair? (v) (consp v))
(defun equalv? (x y) (equal x y))
(defun null? (x) (null x))
(defun the-pos (u s) (position u s :key #'car :test #'equalp))


;;; "si-kanren" starts

;The  `lvar` function  is used  to create  a logical  variable in  the si-kanren
;library.  It takes a single  argument `c` and returns a vector  with `c` as its
;only element.  This vector represents a logical variable and is used in various
;operations related to unification and constraint handling.
(defun lvar (c) (vector c))
(defun lvar? (c) (vectorp c))
(defun lvar=? (x1 x2) (equal (aref x1 0) (aref x2 0)))

;The `walk` function  is used to resolve  logical variables in a  given term `u`
;using a substitution store `s`.  If `u` is a logical variable and it is present
;in `s`,  `walk` recursively looks up its corresponding value in `s` and returns
;the resolved value.  If `u`  is not a logical variable or it  is not present in
;`s`,  `walk`  returns `u`  itself.  Walk and  substitution are  at the  core of
;unification.
(defun walk (u s)
  (if (and (lvar? u)
           (pair? s)
           (the-pos u s))
      (walk (cdr (elt s (the-pos u s))) s)
      u))

;The `ext-s`  function is used  to extend a  substitution store  `s` with  a new
;binding between a logical variable `lvar` and a value `v`. The `ext-s` function
;takes three arguments:  `lvar`,  `v`,  and `s`.  It  returns a new substitution
;store that includes the binding between `lvar` and `v`, as well as the existing
;bindings in `s`. Here's an example of how `ext-s` can be used:
;```
;(ext-s (lvar 2) 5 '((#(0) . 2) (#(1) . 3)))
;```
;This will  return '((#(2) .  5) (#(0) .  2) (#(1) .  3)))),  which represents a
;substitution store with the new binding between `(lvar 2)` and `5`, as well as
;the existing bindings `(#(0) . 2)` and `(#(1) . 3)`.
(defun ext-s (lvar v s)
  `((,lvar . ,v) . ,s))

(defparameter mzero '())

(defun unit (s/c/d) (cons s/c/d mzero))

;The `unify` function is  used to unify two terms in a  logic program.  Here is a
;summary of its functionality:
;Inputs:
;- `u`: The first term to unify
;- `v`: The second term to unify
;- `s`: The substitution store
;Outputs:
;- Returns a new substitution store `s'` that unifies `u` and `v`,  or '(())' if
;the terms cannot be unified.
;Functionality:
;-  First,  the  `walk` function  is  called on  `u`  and  `v`  with  the current
;substitution  store `s`.  This  function recursively  resolves any  variables in
;`u` and `v` to their corresponding values in `s`.
;- The  function then checks  different cases for  unification,  depending on the
;types of `u` and `v:
  ;- If both `u`  and  `v`  are  logical  variables  and  they  refer to the same
  ;variable,  no change is  needed  and  the  current  substitution  store `s` is
  ;returned.
  ;- If `u` is  a logical variable,  it is extended with the  value of `v` in the
  ;substitution store `s`.
  ;- If `v` is  a logical variable,  it is extended with the  value of `u` in the
  ;substitution store `s`.
  ;- If `u`  and `v` are both pairs,  the function  recursively unifies their car
  ;and cdr components.
  ;- If `u` and `v` are atoms and they are equal,  the current substitution store
  ;`s` is returned.
;- Finally, if none of the previous cases apply,  '(())' is returned, indicating
;that the terms cannot be unified.
(defun unify (u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
      ((and (lvar? u) (lvar? v) (lvar=? u v)) s)
      ((lvar? u) (ext-s u v s))
      ((lvar? v) (ext-s v u s))
      ((and (pair? u) (pair? v))
       (let ((s1 (unify (car u) (car v) s)))
         (if (not (equal s1 '(())))
           (unify (cdr u) (cdr v) s1)
           '(()))))
      ((and (equalv? u v) (not (equal s '(())))  s))
      (T '(())))))

;The `call/fresh`  function in si-Kanren is  used to  introduce a  fresh logical
;variable into a  goal.  It takes a function `f` as  an argument,  which is then
;called with the fresh  logical variable as an input.  The result  is a new goal
;that includes the fresh variable.  Here's an example of how `call/fresh` can be
;used:
;```
;(call/fresh (lambda (x) (== x 3)))
;```
;This code  introduces a  fresh variable `x`  and unifies  it with  the constant
;value `3`. The result is a new goal that includes the constraint `x = 3`.
(defun call/fresh (f)
  (lambda (s/c/d)
    (let ((c (c-of s/c/d))
          (d (d-of s/c/d))
          (ty (ty-of s/c/d))
          (a (a-of s/c/d)))
        (funcall (funcall f (lvar c)) `((,(caar s/c/d) . ,(+ c 1)) ,d ,ty ,a)))))

;(defun == (u v)
  ;(lambda (s/c/d)
    ;(let ((s^ (unify u v (s-of s/c/d))))
      ;(if (not (equal s^ '(())))
         ;(normalize-disequality-store
          ;(unit(make-st (cons s^ (c-of s/c/d))(d-of s/c/d)(ty-of s/c/d)(a-of s/c/d))))
         ;mzero))))

;(defun == (u v)
  ;(lambda (s/c/d)
    ;(let ((s^ (unify u v (s-of s/c/d)))))
    ;(let ((d^ (disequality u v (s-of s/c/d)))
          ;(s/c (s/c-of s/c/d))
          ;(d (d-of s/c/d))
          ;(ty (ty-of s/c/d))
          ;(a (a-of s/c/d)))
      ;(if d^
        ;(if (equal d^ '(()))
            ;(unit s/c/d)
         ;(unit (cons (cons (caar s/c/d) (cdar s/c/d))(cdr s/c/d)))
            ;(unit (cons (cons (caar s/c/d) (cdar s/c/d)) (cons d^ (cdr s/c/d)))))
           ;(post-unify-=/= s/c (car d^) d ty a))
         ;(unit(unit (make-st (s-of s/c/d) (c-of s/c/d) (cons d^ (d-of s/c/d))))))
         ;(unit (cons (cons (s-of s/c/d) (c-of s/c/d)) (cons d^ (d-of s/c/d)))))
       ;mzero)))

(defun == (u v) (lambda (st) (==-verify (unify u v (S-of st)) st)))
;(== (lvar 3) 9)
;(funcall * (empty-state))
;(unify (lvar 3) 9 '())
;(run 1 (q)(=/= q 3)(=/= q 4)(=/= q 7)(=/= q 9))
;(run 1 (q)(=/= q 3)(=/= q 4)(=/= q 7)(== q 9))
;(runno 1 (q) (fresh (x y) (== x 9) (== y x)(== q `(,x ,y))))
;(=/= '#(0) 3)
;(call/empty-state (conj+ (=/= (lvar 1) 9)(== (lvar 3) 11) (== (lvar 1) 10)))
;(call/empty-state (conj (== (lvar 1) 9)(== (lvar 3) 11)))
;(call/empty-state (conj (=/= (lvar 1) 9)(=/= (lvar 3) 11)))
;(funcall *)
;The  `mplus`  function  is  used  to  concatenate  two  streams.  It  takes two
;arguments,  `$1` and `$2`,  and returns a stream that contains all the elements
;from both `$1` and `$2`. If `$1` is empty, it simply returns `$2`, otherwise it
;adds  the first  element of  `$1` to  the result  stream and  recursively calls
;`mplus` with  the rest of `$1`  and `$2` as  arguments.  This process continues
;until both  `$1` and `$2`  are empty.  The function  `mplus` is similar  to the
;`append` function in common Lisp,  but is  used specifically for streams in the
;si-kanren library.  If you look carefully  at the definition,  in the recursive
;section the arguments $1 and $2 are swapped.  This is to prevent a (potentially
;infinite) DFS (depth  first search;  I think this is  Prolog style):  if we had
;only (mplus $1  ($2)) and $1 is infinite,  we'll never  reach $2!  In our case,
;instead,  we have  an  unguided,  interleaving  complete  search  (that is both
;complete  and more  useful in  practice  than  are  breadth-first  or iterative
;deepening depth-first search),  in which mplus  alternate the search between $1
;and  $2:  one  little  change  (swapping  two  values)  provides  a  *dramatic*
;difference!
(defun mplus ($1 $2)   ;like appendo
  (cond
    ((null? $1) $2)
    ((functionp $1) (lambda () (mplus $2 (funcall $1))))
    (T (cons (car $1) (mplus (cdr $1) $2)))))

;The `bind`  function in si-Kanren is  used to  combine two  goals together.  It
;takes two arguments,  `$` and  `g`,  where `$` is a goal and  `g` is a function
;that takes a  state `s/c/d` and returns a new  goal.  The `bind` function first
;checks if `$` is an empty list.  If it is, it returns `mzero`, which represents
;a  failure in  Kanren.  If `$`  is  a  function,  it  calls  that  function and
;recursively calls `bind` on the result and `g`.  If `$` is a non-empty list, it
;calls `g`  with the first  element of `$`  and recursively calls  `bind` on the
;rest of `$` and `g`. The results of these two calls to `bind` are then combined
;using `mplus`, which concatenates two streams of states.
(defun bind ($ g) ;like append-map
  (cond
    ((null? $) mzero)
    ((functionp $) (lambda () (bind (funcall $) g)))
    (T (mplus (funcall g (car $)) (bind (cdr $) g)))))


;The `disj`  function in si-Kanren is  used to  combine two  goals together.  It
;takes two  goals,  `g1` and  `g2`,  as arguments  and returns  a new  goal that
;represents the disjunction  (logical OR) of `g1` and  `g2`.  The resulting goal
;will succeed if either `g1` or `g2` succeeds. The `disj` function takes a state
;`s/c/d` as  input and applies  `g1` and `g2`  to that state.  It  then uses the
;`mplus` function to combine the results of  `g1` and `g2` into a single stream,
;representing the disjunction of the  two goals.  The resulting goal returned by
;`disj`  can be  used in  combination with  other  goals  and  functions  in the
;si-Kanren library to create more complex logical programs.
(defun disj (g1 g2)
  (lambda (s/c/d)
    (mplus (funcall g1 s/c/d) (funcall g2 s/c/d))))


;The `conj`  function in si-Kanren is  used to  combine two  goals together.  It
;takes two  goals,  `g1` and  `g2`,  as arguments  and returns  a new  goal that
;represents the conjunction (logical AND)  of `g1` and `g2`.  The resulting goal
;will succeed if both `g1` and `g2` succeed.
;In the implementation of `conj`,  it takes a state `s/c/d` as input and applies
;`g1` to  that state.  It then  uses the `bind`  function to apply  `g2` to each
;resulting state from `g1`. The `bind` function combines the results of `g1` and
;`g2` into a single stream,  representing  the conjunction of the two goals.  By
;calling `bind  (funcall g1 s/c/d) g2`,  we  are calling  `g1` with  the current
;state `s/c/d` and for each resulting  state `s1/c1/d1` from `g1`,  we call `g2`
;with that state to obtain a new stream of states.  This allows us to apply `g2`
;after `g1` has succeeded.  Overall, the `conj` function is used to sequentially
;apply two  goals and combine  their results,  ensuring that  both goals succeed
;before returning the combined result.

(defun conj (g1 g2)
  (lambda (s/c/d)
    (bind (funcall g1 s/c/d) g2)))

;;"si-kanren" stops

;;;;;;;;;;;;;;;;;;;;;;;   Disequality   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun filter (f l) (if (equal l '())
                        '()
                        (if (not (funcall f (car l)))
                            (filter f (cdr l))
                            (cons (car l) (filter f (cdr l))))))

;The `mapm` function is used to apply a function to each element of a list,  and
;collect the results into a new  list.  Here's the code for the `mapm` function:
;This function takes two arguments:  `f`, which is the function to apply to each
;element,  and `l`, which is the list of elements.  It first checks if `l` is an
;empty list. If it is, it returns a unit containing an empty list. Otherwise, it
;calls the function `f` with the first  element of `l`,  and binds the result to
;`v`.  It then recursively calls `mapm` with `f` and the rest of `l`,  and binds
;the  result to  `vs`.  Finally,  it constructs  a unit  containing a  list that
;concatenates `v` and `vs`, and returns this unit.
(defun mapm (f l)
  (if (null? l)
      (unit '())
      (bind (funcall f (car l))
            (lambda (v)
              (bind (mapm f (cdr l))
                    (lambda (vs)
                      (unit (cons v vs))))))))

;The `subtract-s` function is used to subtract one substitution from another. It
;takes  two  substitutions  `s^`  and  `s`   as  arguments  and  returns  a  new
;substitution that contains only  the bindings that are in `s^`  but not in `s`.
;The function checks if `s^` and `s` are equal. If they are, it returns an empty
;substitution.  Otherwise,  it adds the first binding  in `s^` to the result and
;recursively calls `subtract-s` with the rest  of `s^` and `s`.  In other words,
;`subtract-s`  removes  all  the bindings  in  `s`  from  `s^`  and  returns the
;remaining bindings.
(defun subtract-s (s^ s)
  (if (equalp s^ s)
      '()
      (cons (car s^) (subtract-s (cdr s^) s))))

;The `disequality` function takes three arguments: `u`,  `v`, and a substitution
;`s`.  It checks if `u` and `v` are not equal in the given substitution `s`.  If
;they are not equal,  it returns a  modified substitution `s^` that includes the
;mapping between `u` and `v`.  If they are equal, it returns `(())`, indicating)
;that the disequality is not satisfied.
(defun disequality (u v s)
  (let ((s^ (unify u v s)))
      (if (equal s^ '(()))
          '(())
          (let ((d (subtract-s s^ s)))
           (if (null? d)
            '()
             d)))))

;The `(=/=)` function in  `si-kanren` is used to specify that  two terms are not
;equal.  It takes two terms `u` and `v` as arguments and returns a function that
;takes  a  substitution  `s/c/d`  as  an  argument.  The  function  applies  the
;`disequality` function to `u`,  `v`,  and the  substitution `s/c/d` to check if
;`u` and `v` are not equal in the given substitution. If they are not equal, the
;function returns a `unit` containing the modified substitution `s/c/d`. If they
;are equal, the function returns `mzero`, indicating that the conjunction is not
;satisfiable.
;(defun =/= (u v)
  ;(lambda (s/c/d)
    ;(let ((u* (unify u v (s-of s/c/d)))
          ;(s (s-of s/c/d))
          ;(c (c-of s/c/d))
          ;(d (d-of s/c/d)))
      ;(if u*
          ;(if (equal u* '(()))
              ;(unit s/c/d)
              ;(funcall (post-unify-=/= s c d) u*))))))
             ;(unit (cons (cons (caar s/c/d) (cdar s/c/d))(cdr s/c/d))
                ;(unit (cons (cons (caar s/c/d) (cdar s/c/d)) (cons d^ (cdr s/c/d))))
               ;(post-unify-=/= s/c (car d^) d ty a))
         ;(unit(unit (make-st (s-of s/c/d) (c-of s/c/d) (cons d^ (d-of s/c/d)))))
         ;(unit (cons (cons (s-of s/c/d) (c-of s/c/d)) (cons d^ (d-of s/c/d))))
       ;mzero

;(defun post-unify-=/= (S C DS)
  ;(lambda (S+)
    ;(cond ((equal S+ S) mzero)
          ;(t (let ((d (subtract-s  S+ S)))
              ;(unit (make-st (cons S C)
                             ;(filter (lambda (l) (not (null? l)))(cons (car d) DS))
                             ;'()
                             ;'())))))))
(defun =/= (u v)
  (lambda (s/c/d)
    (let ((d^ (disequality u v (s-of s/c/d))))
      (if d^
          (if (equal d^ '(()))
              (unit s/c/d)
              (unit (make-st (s/c-of s/c/d) (cons d^ (d-of s/c/d)) (ty-of s/c/d)(a-of s/c/d))))
              ;(unit (cons (cons (s-of s/c/d) (c-of s/c/d)) (cons d^ (d-of s/c/d)))))
       mzero))))


;(unify '(#(3) . 6) '(42 . #(4)) '((#(1) . 11) (#(2) . 5)(#(0) . 10)))
;(unify '(#(2) . #(3)) '(#(4) . 6) '((#(3) . 5)))
;(subtract-s * '((#(3) . 5)))
;(disequality #(3) 10 '((#(1) . 11) (#(2) . 5)(#(0) . 10)))
;(unify #(0) 9 '((#(1) . 11) (#(2) . 5)))
;(disequality #(0) 9 '((#(1) . 11) (#(2) . 5)))
;(subtract-s (unify #(0) 9 '((#(1) . 11) (#(2) . 5))) '((#(1) . 11) (#(2) . 5)))
;(unify '#(3) 5 '((#(3) . 5)))
;(cons * 0)
;(==  '#(4) 11)
;(runno 1 (q)(fresh (x y) (=/= `(,x . 7) `(5 . ,y))))
;(runno 1 (q)(fresh (x y) (== q `(,x ,y))(=/= `(,x . 7) `(5 . ,y))))
;(runno 1 (q)(fresh (x y z) (== z 9) (== q `(,x ,y))(=/= `(,x . 7) `(5 . ,y))))
;(runno 1 (q)(fresh (x y z)(== q `(,x ,y))(=/= `(,x . 7) `(5 . ,y)) (== z 9)))
;(runno 1 (q)(fresh (x y z)(== q `(,x ,y))(== x 9)(=/= `(,x . 7) `(,z . ,y)) (== z 9)(== y 7)))
;(runno 1 (q)(fresh (x y) (=/= `(,x . 7) `(5 . ,y)) (== q `(,x ,y))))
;(run* (q) (=/= 4 q)(=/= 3 q))
;(runno 1 (q)
  ;(fresh (x y)
    ;(== `(,x ,y) q)
    ;(=/= `(,x ,y) `(5 6))
    ;(=/= x 5)))
;(load "~/test-suite.lisp")
;(run 1 (q)
  ;(fresh (x y)
    ;(== `(,x ,y) q)
    ;(=/= x 5)
    ;(=/= `(,x ,y) `(5 6))))
;(runno 1 (q)(fresh (x y) (=/= `(,x . 7) `(5 . ,y)) (== x 5)))
;(run 1 (q)(fresh (x y) (=/= x 5)(== x 5)))
;(run 1 (q)(fresh (x y) (=/= `(,x . 7) `(5 . ,y)) (== x 5)(== y 7)))
;(unify* '((#(2) . 5))  '((#(0) . #(1)) (#(2) . 5)))
;(reform-d  '(((#(2) . 5))) '() '((#(0) . #(1)) (#(2) . 5)))


;(funcall * (empty-state))
;(funcall * **)
;(funcall * (car **))
;(funcall * '((#(2) . 5)))
;(funcall * **)
;(== '#(3) 9)
;(funcall * '((((#(4) . 4)(#(5) . 9) (#(3) . 7)(#(2) . 3)) . 9) ((#(1) . 11) (#(2) . 5)(#(9) . 10)) () ()))
;(runno 1 (q) (fresh (x y) (== x 4) (== y 9) (=/= q 5) (=/= q 3)(== q `(,x  ,y))))
;(walk* #(1) (caar *))
;(runno 1 (q) (fresh (x y) (== `(,x 4) `(9 ,y)) (=/= q 5) (=/= q 3)(== q `(,y . ,x))))
;(runno 1 (q) (fresh (x y) (== x 4) (== y 9)))
;(== (lvar 1) 2)
;(==  `(#(2) 3) `(5 #(3)))
;(funcall * (empty-state))
;(== #(4) 9)
;(funcall * **)
;(filter (lambda (l) (not (null? l)))(cdr **))
;(cadr ***)
;The `normalize-disequality-store` function  takes a store `s/c/d`  as input and
;applies the `disequality` function to each  pair of variables in the store.  It
;filters  out any  empty results  and returns  a new  store with  the normalized
;disequalities.  In  this  code,  the  `mapm`  function  is  used  to  apply the
;`disequality` function  to each pair  of variables in  the store.  The `filter`
;function is  used to remove any  empty results.  The filtered  results are then
;combined with  the original  store to create  a new  store with  the normalized
;disequalities.  The `normalize-disequality-store` function is  part of the type
;constraint section of the code and is used to handle constraints related to the
;equality and disequality of variables in the Kanren system.
;(defun normalize-disequality-store (s/c/d)
 ;(bind (mapm (lambda (es)
               ;(let ((d^ (disequality (mapcar #'car es)
                                      ;(mapcar #'cdr es)
                                      ;(s-of s/c/d))))
                  ;(if d^
                      ;(if (equal d^ '(()))
                          ;'(())
                          ;d^)
                      ;mzero)))
             ;(filter (lambda (l) (not (null? l)))
                     ;(cadr s/c/d)))
       ;(lambda (d)
         ;(unit (make-st  (s/c-of s/c/d) d (ty-of s/c/d) (a-of s/c/d))))))

;;;;;;;;;;;;;;;;;;;;;;;  ALTERNATIVE NORMALIZATION   ;;;;;;;;;;;;;;;;;;;;;;;

;(unify   (lvar 2)  4 '((#(0) . #(1)) (#(2) . 3)(#(9) . 8)))
;(subtract-s * '((#(0) . #(1)) (#(2) . 3)(#(9) . 8)))
;(disequality   (lvar 2)  3 '((#(0) . #(1)) (#(2) . 3)(#(9) . 8)))
;(unify   (lvar 3)  3 '((#(0) . #(1)) (#(2) . 3)(#(9) . 8)))
;(unify   (lvar 2)  3 '((#(0) . #(1)) (#(2) . 3)(#(9) . 8)))
;(subtract-s * '((#(0) . #(1)) (#(2) . 3)(#(9) . 8)))
;(unify   (lvar 2)  3 '((#(0) . #(1)) (#(2) . 3)(#(9) . 8)))
;(disequality   (lvar 3)  3 '((#(0) . #(1)) (#(2) . 3)(#(9) . 8)))
;(disequality   (lvar 2)  4 '((#(0) . #(1)) (#(2) . 3)(#(9) . 8)))
;(unify* '((#(3) . 5) (#(3) . 7)) '((#(0) . #(1)) (#(2) . 3)))
;(subtract-s * '((#(0) . #(1)) (#(2) . 3)))
;(reform-d '((#(3) . 4) (#(4) . 7)) '() '((#(0) . #(1)) (#(2) . 3)))

;(reform-d '(((#(2) . 3))) '() '((#(0) . #(1)) (#(2) . 3)))
;(reform-d '(((#(3) . 8))) '() '((#(0) . #(1)) (#(2) . 5) (#(3) . 7)))

;(runno 1 (q) (fresh (x y) (=/= x 5) (=/= y 9) (== q 3)))
;(reform-d '(((#(2) . 3)) ((#(4) . 7))) '() '((#(0) . #(1)) (#(2) . 3)))
;(unify* '((#(2) . 3) (#(4) . 7))  '((#(0) . #(1)) (#(2) . 3)))
;(unify* '((#(3) . 4) (#(4) . 7))  '((#(0) . #(1)) (#(2) . 3)))
;(reform-d '(((#(2) . 3))((#(1) . 7)) ((#(1) . 4))) '() '((#(0) . #(1))(#(2) . 3)))
;(reform-d '(((#(2) . 4))((#(1) . 7)) ((#(1) . 4))) '() '((#(0) . #(1))(#(2) . 3)))
;(reform-d '(((#(5) . 3) (#(3) . cat))) '() '((#(0) . #(1))(#(5) . 9) (#(4) . cat)))
;(reform-d '(((#(5) . 3) (#(4) . cat))) '() '((#(0) . #(1))(#(5) . 9) (#(4) . cat)))
;(flatten* * 1)
;(unify* (car '(((#(5) . 3)) ((#(3) . 7)))) '((#(0) . #(1)) (#(2) . 3)))
;(unify* '((#(2) . 4) (#(4) . 7)) '((#(0) . #(1)) (#(2) . 3)))
;(unify '#(2)  4 '((#(0) . #(1)) (#(2) . 3)))
;(unify* '((#(4) . 4)(#(5) . 9) (#(3) . 7)(#(8) . 4)) '((#(0) . #(1)) (#(4) . 3)))
;(unify* '((#(4) . 4)(#(5) . 9)(#(2) . 4) (#(3) . 7)) '((#(0) . #(1)) (#(2) . 3)))
;(unify* '((#(4) . 4)(#(5) . 9)(#(2) . 3) (#(3) . 7)) '((#(0) . #(1)) (#(2) . 3)))
;(unify #(2)  3 '((#(0) . #(1)) (#(2) . 4)))
;(unify '#(2) 3 '((#(0) . #(1)) (#(2) . 3)))
;(subtract-s * '((#(0) . #(1)) (#(2) . 3)))
;(cons * '((#(0) . #(1)) (#(2) . 3)))
;(normalize-disequality-store *)


;;;;;;;;;;;;;;;;;;;;;;;;;;   DISEQUALITY DI COPPIA ;;;;;;;;;;;;;;;;;;;;

;(unify '(#(5) . 3) '(9 . #(2)) '((#(0) . #(1)) (#(3) . cat)))
;(subtract-s * '((#(0) . #(1)) (#(3) . cat)))
;(unify* '((#(1) 9)) '((#(2) . 5) (#(3) . cat)))
;(unify '(#(5) . 3) '(9 . #(2)) *)
;(subtract-s  * **)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(runno 1 (q) (fresh (x y)(== q `(,x ,y))(=/= `(,x 3) `(cat ,y))))
;(runno 1 (q) (fresh (x y)(== q 9)(=/= `(,x 3) `(cat ,y))))
;(runno 1 (q) (fresh (x y)(=/= `(,x 3) `(cat ,y))(== y 3) (== q `(,x ,y))(== x 'cat)))
;(runno 1 (q) (fresh (x y)(=/= `(,x 3) `(cat ,y))(== y 3)))
;(runno 1 (q) (fresh (x y)(== x q)(== 3 y) (== x 'cat)(=/= `(,x 3) `(cat ,y))))
;(S-OF *)
;(==-verify   (unify #(3) 3 (unit (s-of *))) *)
;(funcall * (unit **))
;(car *)
;(cadr *)
;(cadr *)
;(normalize-disequality-store  *)
;(d-of *)
;(flatten* * 1)
;(runno 1 (q) (fresh (x y)(== x 5)(== y x) (== q 9)))
;(runno 1 (q) (fresh (x y)(== x 5)(== y x)(=/= q x)))
;(runno 1 (q) (fresh (x y)(== x 5)(== y x)(=/= q y)))
;(runno 1 (q) (fresh (x y) (=/= `(,x 9)`(8 ,y)) (=/= q 4)(=/= q 6)(=/= 5 q)(=/= q y)))
;(reform-d '(((#(1) . 5)) ((#(1) . 6))) '() (unify #(1) 1 '((#(0) . #(1)))))
;(runno 1 (q) (fresh (x y) (=/= `(,x 9)`(8 ,y))(=/= q 4)(=/= q 6)(=/= 5 q)(== q 1)))
;(car *)
;(s-of *)
;(d-of *)
;(caar *)
;(runno 1 (q) (=/= q 4)(=/= q 6)(=/= 5 q)(== q 9))
;(runno 1 (q) (=/= q 4)(=/= q 6)(=/= 5 q))
;(runno 1 (q) (fresh (x) (== x 6) (== q x)))
;(s-of *)
;(== (lvar 1) 6)
;(funcall * **)
;(car *)
;(d-of *)
;(flatten* * 1)
;(runno 1 (q) (=/= q 4)(=/= q 6)(== 5 q))
;(runno 1 (q) (=/= q '(4 5))(== q '(4 5)))
;(runno 1 (q)(== q 3) (=/= q 4)(=/= q 6)(=/= 5 q))
;(runno 1 (q)(== q 3))
;(runno 1 (q) (fresh (x y) (== y 2) (=/= `(,x 2) `(9 ,y))))
;(runno 1 (q) (fresh (x y)(=/= `(,x 2) `(9 ,y)) (== y 2)))
;;(d-of (car *))
;(apply 'concatenate 'list *)
;(mapm (lambda (x) (cons (numberp x) '())) '(1 2 3))

;(bind (mapm (lambda (x) (cons (numberp x) '()))
 ;'(1 2 3))
 ;(lambda (ty) (cons ty '(pippo))))

;(let ((s^ '((#(2) . 10)(#(0) . #(2)) (#(1) . #(0)))))
 ;(bind (mapm (lambda (x) (let ((d^ (disequality (car x) (cdr x) s^)))
               ;(if d^
                   ;(if (equal d^ '(()))
                      ;'(())
                      ;d^)
                   ;mzero)))
           ;'((#(2) . 7) (#(5) . 11)(#(4) . 10)(#(2) . 9)))
   ;(lambda (d) (cons s^ (cons (filter (lambda (l) (not (null? l)))d) nil)))))
;(unit *)
;(mk-reify (normalize-conde *))
;(let ((s^ '((#(2) . 10)(#(0) . #(2))(#(3) . cat)(#(5) . 3) (#(1) . #(0)))))
 ;(bind (mapm (lambda (x) (let ((d^ (disequality (car x) (cdr x) s^)))
                 ;(if d^
                     ;(if (equal d^ '(()))
                        ;'(())
                        ;d^)
                     ;mzero)))
           ;'((#(2) . 7) (#(5) . 11)(#(4) . 10)(#(2) . 9)((#(5) . 3) (#(3) . cat))))
   ;(lambda (d) (cons s^ (cons (filter (lambda (l) (not (null? l)))d) nil)))))
;(normalize-disequality-store '((((#(2) . 10)(#(0) . #(2))(#(3) . cat)(#(5) . 3) (#(1) . #(0)))  . 8)
                    ;(((#(2) . 7) (#(5) . 11)(#(4) . 10)(#(2) . 9)((#(5) . 3) (#(3) . cat))))
                    ;() ()))

;(normalize-disequality-store '((((#(2) . 10)(#(0) . #(2))(#(3) . cat)(#(5) . 3) (#(1) . #(0)))  . 8)
                    ;(((#(2) . 7) (#(5) . 11)(#(4) . 10)(#(2) . 9)))
                    ;() ()))
(defun unify* (d S)
  (cond ((null? d) S)
        ((let ((s^ (unify (caar d) (cdar d) S)))
           (when (not (equal s^ '(())))
            (funcall (lambda (S) (unify* (cdr d) S)) s^))))
        (T nil)))

(defun reform-D (D D^ S)
  (cond ((null? D) D^)
        ((let ((d* (unify* (car D) S)))
           (if (equal d* nil)
               nil
               (funcall (lambda (S^)
                          (if (equalp S S^)
                              "err"
                              (let ((d+ (subtract-s S^ S)))
                                (reform-D (cdr D) (cons d+ D^) S)))) d*))))
        (T (reform-D (cdr D) D^ S))))

;(defun reform-D (D D^ S)
  ;(cond ((null? D) D^)
        ;((let ((d* (unify* (car D) S)))
           ;(if (or (equal d* '(())) (equal d* nil))
               ;nil
               ;(funcall (lambda (S^)
                          ;(if (equalp S S^)
                              ;nil
                              ;(let ((d+ (subtract-s S^ S)))
                                ;(reform-D (cdr D) (cons d+ D^) S)))) d*))))
        ;(t (reform-D (cdr D) D^ S))))

(defun ==-verify (S+ st)
  (cond ((equal S+ '(())) mzero)
        ((equalp (S-of st) S+) (unit st))
        ((let ((rd (reform-D (d-of st) '() S+)))
            (funcall (lambda (D)
                       (cond ((equal rd "err") nil)
                             ((let ((rt (reform-T (ty-of st) S+)))
                                (funcall (lambda (TY)
                                           (cond ((equal TY "err") mzero)
                                                 ((equal TY "mnt") st)
                                                 ((equal TY "rmv") 'pippo)
                                                 (T (unit (make-st
                                                                (cons S+ (C-of st))
                                                                (rem-subsumed-D<T TY D)
                                                                TY
                                                                (a-of st)))))) rt))))) rd)))
       (t mzero)))

;(defun ==-verify (S+ st)
  ;(cond ((equal S+ '(())) mzero)
        ;((equalp (S-of st) S+) (unit st))
        ;((if (not (null? (d-of st)))
             ;(let ((rd (reform-D (d-of st) '() S+)))
                  ;(if (equal rd 'err)
                      ;nil
                      ;(unit (make-st
                                  ;(cons S+ (C-of st))
                                  ;rd
                                  ;(ty-of st)
                                  ;(a-of st)))))
            ;(unit(make-st (cons S+ (c-of st)) (d-of st) (ty-of st) (a-of st)))))))
;(defun == (u v) (lambda (st) (==-verify (unify u v (S-of st)) st)))
;;;;;;;;;;;;;;;;;;;;;;   Type constraint     ;;;;;;;;;;;;;;;;;

(defun tag=? (t0 t1)
  (eq t0 t1))

(defun tag-of (ty)
  (cadr ty))

(defun pred-of (ty)
   (cddr ty))

;The `make-type-constraint` function  is used to create a  type constraint for a
;logical variable. It takes four arguments: `tag`, `pred`, `u`, and `st`.
;The `tag` argument represents the tag of the type constraint, which can be used
;to identify  the type  of the constraint.  The  `pred` argument  represents the
;predicate function used to check if a value satisfies the constraint.
;The `u` argument represents the logical  variable for which the type constraint
;is  being  created.  It  is  passed  to  the  `walk`  function  along  with the
;substitution `S` from the state `st` to resolve the value of `u` in the current
;substitution.
;The `st` argument represents the current  state in the si-Kanren system.  It is
;used to access the substitution store `S` and the type constraint store `TY`.
;Inside the  `make-type-constraint` function,  `u` is resolved  using the `walk`
;function,  and the resulting value is  checked against the constraint predicate
;using the `pred`  function.  If  the  value  satisfies  the constraint,  a unit
;containing the unchanged state `st` is returned.  If the value does not satisfy
;the constraint,  `mzero`  is returned,  indicating that the  conjunction is not
;satisfiable.
;Overall, the `make-type-constraint` function is used to define type constraints
;for logical variables and check if those constraints are satisfied in the given
;state.
(defun make-type-constraint (tag pred)
  (lambda (u)
    (lambda (st)
      (let ((S (S-of st)))
        (let ((u (walk u S)))
          (cond ((lvar? u)
                 (let ((t/x (make-type-constraint/x u tag pred st)))
                    (if t/x (unit t/x)
                            mzero)))
                ((pair? u) mzero)
                (T
                  (cond
                    ((funcall pred u) (unit st))
                    (T mzero)))))))))

;The `ext-TY` function is  used to extend the type constraint  store `TY` with a
;new type constraint.  It takes four arguments: `x`, which is the variable to be
;constrained;  `tag`,  which is the tag of the constraint;  `pred`, which is the
;predicate of the  constraint;  and `TY`,  which is the  current type constraint
;store.
;The function first checks if the type constraint store `TY` is empty. If it is,
;it simply returns a new store with the new constraint.
;If `TY` is not empty,  the function checks  each type constraint in `TY` to see
;if it matches the variable `x`.  If it does,  the function checks if the tag of
;the constraint is the same as the new constraint's tag.  If it is, the function
;returns an empty store,  as there is no need to add a duplicate constraint.  If
;the tags  are different,  it  means there  is a  conflict between  the existing
;constraint and the new constraint, so the function returns an error.
;If the current constraint in `TY` does not match `x`,  the function recursively
;calls `ext-TY`  with the rest of  `TY`.  This allows  the function  to continue
;checking the remaining constraints in the store.
;In summary, `ext-TY` extends the type constraint store with a new constraint if
;there are no  conflicts or duplicates.  If there is  a conflict,  it returns an
;error.
(defun ext-TY (x tag pred TY)
  (cond
   ; Ran out of type constraints without any conflicts, add new type constraint
   ; to the store (because the type constraint store is empty).
   ((null? TY) `((,x . (,tag . ,pred))))
   (T (let ((ty (car TY))
            (TY-next (cdr TY)))
        (let ((t-tag (tag-of ty)))
          (cond
            ; Is the current constraint on x?
            ((equalp (car ty)  x)
             (cond
               ; Is it same as the new constraint? Then do not extend the store
               ((tag=? t-tag tag) '())
               ; Is it conflicting with the new constraint? Then fail.
               (T "err")))
             ; The current constraint is not on x, continue going through
             ; rest of the constraints
           (T (ext-TY x tag pred TY-next))))))))

;The following two have to move in wrappers.lisp when ready;;;;;;;;;;;;;;;;;;;;
;The `subsumed-d-pr?` function checks if a disequality constraint is subsumed by
;any existing constraints in the type constraint store (`TY`). It takes the type
;constraint store  (`TY`) as  an argument and  returns a  function that  takes a
;disequality constraint (`d-pr`) as an argument.
;In  the function,  it  first retrieves  the second  element of  the disequality
;constraint,  which represents the value `u`  in the disequality `(!= u v)`.  It
;then checks if `u` is a logical variable. If it is, it returns `()`, indicating
;that the  constraint is not subsumed.  If  `u` is  not a  logical variable,  it
;searches for  a matching constraint in  the type constraint  store (`TY`) using
;the value `u` as the key.  If a matching constraint is found,  it checks if the
;predicate of the constraint (defined by the `pred-of` function) is satisfied by
;the value `u`. If it is, it returns `()`, indicating that the constraint is not
;subsumed.  If the predicate is not satisfied,  it returns `t`,  indicating that
;the constraint is subsumed.
;`subsumed-d-pr?  and rem-subsumed-D<T are  used in the `make-type-constraint/x`
;function to handle type constraints and disequalities in the si-Kanren system.
(defun subsumed-d-pr? (TY)
  (lambda (d-pr)
    (let ((u (cdr d-pr)))
      (cond
         ; We want the disequality to be between a variable and a constant,
         ;can ignore constraints between two variables.
                     ((lvar? u) '())
                     (T (let ((sc (assoc  (car d-pr) TY :test #'equalp)))
                          (and sc
                            (cond
                              ((funcall (pred-of sc) u) ())
                              (T T)))))))))

;The `rem-subsumed-D<T`  function removes subsumed  disequality constraints from
;the disequality store (`D`).  It takes the type constraint store (`TY`) and the
;disequality store (`D`)  as  arguments.  It  uses  the  `delete-if` function to
;remove  disequality constraints  from the  store  (`D`)  that  are  subsumed by
;constraints in the type constraint  store (`TY`).  It uses the `subsumed-d-pr?`
;function to determine if a constraint is subsumed.
(defun rem-subsumed-D<T (TY D)
  (delete-if (subsumed-d-pr? TY) D))

;The `make-type-constraint/x` function takes four arguments: `u`, `tag`, `pred`,
;and `st`.
;It  first extends  the type  constraint  store  `TY`  with  the  new constraint
;represented by `u`, `tag`, and `pred` using the `ext-TY` function.
;Then,  it calls a lambda function that takes `T+` as its argument.  Inside this
;lambda function, it checks three conditions:
;1. If `T+` is an empty list, it returns the original state `st` since there are
;no new constraints to add.
;2.  If `T+` is equal to the string "err",  it returns an empty list, indicating
;that the new constraint is conflicting with existing constraints.
;3.  Otherwise,  it creates a new state  with the extended type constraint store
;`TY-next` that  includes the new  constraint and the  existing constraints.  It
;also removes any subsumed constraints from  the disequality store `D` using the
;`rem-subsumed-D<T` function.
;Finally,  it calls the  lambda function with the extended  type constraint `ty`
;and returns the result.
(defun make-type-constraint/x (u tag pred st)
     (let ((ty (ext-TY u tag pred (TY-OF st))))
          (funcall (lambda (T+)
                     (cond ((null? T+) st)
                           ((equal T+ "err") '())
                           (T (let ((TY-next (append T+ (TY-of st)))
                                    (D (rem-subsumed-d<t T+ (D-of st))))
                                (make-st (S/C-of st) D TY-next (a-of st)))))) ty)))


;The `symbolo` function  is  used  to  create  a  type  constraint for a logical
;variable `u` that indicates that `u` must be a symbol.  It is implemented using
;the  `make-type-constraint`  function,  which  takes  three  arguments:  `tag`,
;`pred`,  and `st`.  In this case,  the `tag` is set to `'sym` and the `pred` is
;set to the  function  `symbolp`,  which  checks  if  a  value is a symbol.  The
;`make-type-constraint` function is then called with `u`, `'sym`, `symbolp`, and
;the current  state `st` as arguments.  This  creates a type  constraint for `u`
;that is added to the type constraint store in the state `st`.
(defun symbolo (u) (funcall (make-type-constraint 'sym #'symbolp) u))

;The `numbero`  function is a  type constraint function  that checks if  a given
;term `u` is a number.  It uses  the `make-type-constraint` function to create a
;type constraint that specifies the `num` tag and the `numberp` predicate.  This
;type constraint is then applied to the term `u` in the `funcall` expression.
;If the  term `u` satisfies the  type constraint  (i.e.,  it is  a number),  the
;`make-type-constraint`  function   returns  a   unit  containing   the  current
;substitution  `st`.   If  `u`  does  not  satisfy  the  type  constraint,   the
;`make-type-constraint`   function   returns   `mzero`,   indicating   that  the
;conjunction is not satisfiable.
;Overall, the `numbero` function is used to add a type constraint that checks if
;a term is a number in the si-Kanren system.
(defun numbero (u) (funcall (make-type-constraint 'num #'numberp) u))

;(runno 1 (q) q) ;; funziona
;(runno 1 (q) (numbero q)) ;; funziona
;(run 1 (q)(== q 'cat)(== q 3)) ;; funziona
;(runno 1 (q)(== q 'cat)(symbolo q)) ;; funziona
;(run 1 (q)(== q 'cat)(symbolo q)) ;; funziona
;(run 1 (q)(symbolo q)(== q 'cat)) ;;  funziona
;(runno 1 (q)(symbolo q)(== q 'cat)) ;;  funziona
;(run 1 (q)(symbolo q)(== q 3)) ;; funziona
;(runno 1 (q)(symbolo q)(== q 3)) ;; funziona
;(run 1 (q)(== q 'cat)(numbero q)) ;; funziona
;(runno 1 (q)(numbero q)(== q 'cat)) ;; funziona
;(run 1 (q) (numbero q)(== q 3)) ;; funziona
;(runno 1 (q) (numbero q)(== q 3)) ;; funziona
;(run 1 (q)(== q 3) (numbero q)) ;;funziona
;(runno 1 (q)(== q 3) (numbero q)) ;;funziona
;(runno 1 (q)(fresh (x) (numbero x)(== q 3) (numbero q))) ;;funziona
;(runno 1 (q) (=/= 'cat q) (numbero q)) ;; non funziona
;(runno 1 (q) (numbero q) (=/= 'cat q)) ;; non funziona
;(runno 1 (q) (fresh (a) (=/= 'cat a) (numbero a)))  ;; non funziona
;(runno 1 (q) (fresh (x) (numbero x) (symbolo q)))
;(runno 1 (q) (fresh (x)(=/= q 'cat) (numbero x) (symbolo q)))
;(runno 1 (q) (fresh (x)(=/= q 3) (numbero x) (symbolo q)))
;(runno 1 (q) (fresh (x)(== q 3) (numbero x) (symbolo q)))
;(runno 1 (q) (fresh (x)(== q 3)(== x 3) (numbero q)))
;(runno 1 (q) (fresh (x)(== q 3)(numbero x) (numbero q)))
;(runno 1 (q) (fresh (x)(== q 3)(== x 3) (numbero x) (numbero q)))
;(runno 1 (q) (fresh (x y)(== `(,x 9) `(8 ,y))(== q `(,x ,y))(symbolo y)))
;(runno 1 (q) (fresh (x y)(symbolo y)(== `(,x 9) `(8 ,y))(== q `(,x ,y))))
;(runno 1 (q) (fresh (x y)(symbolo y)(== `(,x cat) `(8 ,y))(== q `(,x ,y))))
;(runno 1 (q) (fresh (x y w z)
                ;(symbolo y)
                ;(numbero x)
                ;(numbero w) (== '(8 cat) `(,x ,y))))
;(runno 1 (q) (fresh (x)(== q 3)(== x 3) (numbero x) (symbolo q)))
;(runno 1 (q) (fresh (x)(== q 3) (numbero x) (numbero q)(== x 9)))
;(runno 1 (q) (fresh (x)(== q 3) (numbero q)))
;(run 1 (q) (fresh (x) (numbero x) (symbolo q)))
;(reform-t '((#(1) sym . symbolp)) '((#(1) . 3) (#(0) .#(1))))
;(reform-t '((#(2) num . numberp)) '((#(1) . 3) (#(0) .#(1))))
;(ext-ty #(2) 'num #'numberp '((#(2) sym . symbolp)))
;(runno 1 (q) (fresh (x) (== x q) (symbolo q) (symbolo x)))
;(runno 1 (q) (fresh (x) (symbolo q) (== 'y x) (== x q)))
;(runno 1 (q) (fresh (x) (== q x) (symbolo q)))
;(reform-t '((#(2) sym . symbolp)) '((#(2) . 5) (#(1) . #(2)) (#(0) .#(1))))
;(runno 1 (q) (fresh (x) (== q x) (symbolo q) (== 5 x)))
;(defun reform-T (TY S)
 ;(cond ((null? TY) '())
       ;((let ((rt (reform-T (cdr TY) S)))
          ;(funcall (lambda (T0)
               ;(let ((u (walk (car (car TY)) S))
                     ;(tag (tag-of (car TY)))
                     ;(pred (pred-of (car TY))))
                 ;(cond ((lvar? u)
                        ;(cond ((let ((et (ext-TY u tag pred T0)))
                                ;(funcall (lambda (T+) (append T+ T0)) et)))
                              ;(T "erri0")))
                       ;(T (when (not (and (funcall pred  u) T0)) nil))))) rt)))
       ;(T 'mnt)))

(defun reform-T (TY S)
  (cond ((null? TY) '())
        ((let ((rt (reform-T (cdr TY) S)))
           (funcall (lambda (T0)
                      (let ((u (walk (car (car TY)) S))
                            (tag (tag-of (car TY)))
                            (pred (pred-of (car TY))))
                        (cond ((lvar? u)
                               (cond ((let ((et (ext-TY u tag pred T0)))
                                       (cond ((equal et "err") mzero)
                                             ((equal et nil) rt)
                                             (T (funcall (lambda (T+) (append T+ T0)) et)))))
                                     (T "err")))
                              (T (if (funcall pred  u)
                                     "rmv"
                                     "err"))))) rt)))
        (T "mnt")))
