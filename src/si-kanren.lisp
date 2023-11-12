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
      ((and (equalv? u v) (not (equal s '(()))) s))
      (t '(())))))

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
    (let ((c (cdar s/c/d))
          (d (cdr s/c/d)))
        (funcall (funcall f (lvar c)) `((,(caar s/c/d) . ,(+ c 1)) . ,d)))))

(defun == (u v)
  (lambda (s/c/d)
    (let ((s (unify u v (caar s/c/d))))
      (if (not (equal s '(())))
          (normalize-disequality-store
           (cons (cons s (cdar s/c/d))(cdr s/c/d)))
          mzero))))

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
;instead,  we have  an interleaving complete  search (aka breadth  first search:
;BFS),  in which mplus alternate the search between $1 and $2: one little change
;(swapping two values) provides a *dramatic* difference!
(defun mplus ($1 $2)   ;like appendo
  (cond
    ((null? $1) $2)
    ((functionp $1) (lambda () (mplus $2 (funcall $1))))
    (t (cons (car $1) (mplus (cdr $1) $2)))))

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
    (t (mplus (funcall g (car $)) (bind (cdr $) g)))))


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

;;;;;;;;;;;;;;;;;;;;;;;   Disequality ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
       (if s^
          (if (equal s^ '(()))
              '(())
              (let ((d (subtract-s s^ s)))
               (if (null? d)
                '()
                 d)))
         '(()))))

;The `(=/=)` function in  `si-kanren` is used to specify that  two terms are not
;equal.  It takes two terms `u` and `v` as arguments and returns a function that
;takes  a  substitution  `s/c/d`  as  an  argument.  The  function  applies  the
;`disequality` function to `u`,  `v`,  and the  substitution `s/c/d` to check if
;`u` and `v` are not equal in the given substitution. If they are not equal, the
;function returns a `unit` containing the modified substitution `s/c/d`. If they
;are equal, the function returns `mzero`, indicating that the conjunction is not
;satisfiable.
(defun =/= (u v)
  (lambda (s/c/d)
    (let ((d^ (disequality u v (caar s/c/d))))
      (if d^
        (if (equal d^ '(()))
         (unit (cons (cons (caar s/c/d) (cdar s/c/d))(cdr s/c/d)))
         (unit (cons (cons (caar s/c/d) (cdar s/c/d)) (cons d^ (cdr s/c/d)))))
       mzero))))

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
(defun normalize-disequality-store (s/c/d)
  (bind (mapm (lambda (es)
                (let ((d^ (disequality (mapcar #'car es)
                                       (mapcar #'cdr es)
                                       (caar s/c/d))))
                   (if d^
                       (if (equal d^ '(()))
                           '(())
                           (unit d^))
                       mzero)))
              (filter (lambda (l) (not (null? l)))
                      (cdr s/c/d)))
        (lambda (d)
          (unit (cons (cons (caar s/c/d) (cdar s/c/d)) d)))))

;;;;;;;;;;;;;;;;;;;;;;   Type constraint     ;;;;;;;;;;;;;;;;;

;(defun make-type-constraint (tag pred)
  ;(lambda (u)
    ;(lambda (st) (let ((S (caar st))(C (cdar st)) (D (cadr st)) (T (T-of st)))
                   ;))))
