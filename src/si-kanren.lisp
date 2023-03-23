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

(defun lvar (c) (vector c))
(defun lvar? (c) (vectorp c))
(defun lvar=? (x1 x2) (equal (aref x1 0) (aref x2 0)))

(defun walk (u s)
  (if (and (lvar? u)
           (pair? s)
           (the-pos u s))
      (walk (cdr (elt s (the-pos u s))) s)
      u))

(defun ext-s (lvar v s)
  `((,lvar . ,v) . ,s))

(defparameter mzero '())

(defun unit (s/c/d) (cons s/c/d mzero))

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

(defun mplus ($1 $2)   ;like appendo
  (cond
    ((null? $1) $2)
    ((functionp $1) (lambda () (mplus $2 (funcall $1))))
    (t (cons (car $1) (mplus (cdr $1) $2)))))

(defun bind ($ g) ;like append-map
  (cond
    ((null? $) mzero)
    ((functionp $) (lambda () (bind (funcall $) g)))
    (t (mplus (funcall g (car $)) (bind (cdr $) g)))))

(defun disj (g1 g2)
  (lambda (s/c/d)
    (mplus (funcall g1 s/c/d) (funcall g2 s/c/d))))

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

(defun mapm (f l)
  (if (null? l)
      (unit '())
      (bind (funcall f (car l))
            (lambda (v)
              (bind (mapm f (cdr l))
                    (lambda (vs)
                      (unit (cons v vs))))))))

(defun subtract-s (s^ s)
  (if (equalp s^ s)
      '()
      (cons (car s^) (subtract-s (cdr s^) s))))

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

(defun =/= (u v)
  (lambda (s/c/d)
    (let ((d^ (disequality u v (caar s/c/d))))
      (if d^
        (if (equal d^ '(()))
         (unit (cons (cons (caar s/c/d) (cdar s/c/d))(cdr s/c/d)))
         (unit (cons (cons (caar s/c/d) (cdar s/c/d)) (cons d^ (cdr s/c/d)))))
       mzero))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
