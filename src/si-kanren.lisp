(defpackage :si-kanren
    (:use :common-lisp)
    (:export
      #:run
      #:run*
      #:runi
      #:fresh
      #:conde
      #:==
      #:=/=
      #:symbolo
      #:numbero
      #:absento))

(in-package :si-kanren)

(defun pair? (v) (consp v))
(defun equalv? (x y) (equal x y))
(defun null? (x) (null x))
(defun the-pos (u s) (position u s :key #'car :test #'equalp))


;;;;;;;;;;;;;;; "si-kanren" (core microKanren) starts   ;;;;;;;;;;;;;;;;;;;;;;;

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

(defun unit (st) (cons st mzero))

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

(defun call/fresh (f)
  (lambda (st)
    (let ((c (c-of st))
          (d (d-of st))
          (ty (ty-of st))
          (a (a-of st)))
        (funcall (funcall f (lvar c)) `((,(caar st) . ,(+ c 1)) ,d ,ty ,a)))))


(defun == (u v)
  (lambda (st)
    (let ((s^ (unify u v (s-of st))))
      (if (not (equal s^ '(())))
          (let ((nds (normalize-d<s/t/a #'disequality s^ (d-of st) (s-of st))))
            (if (member 'err nds)
                nil
                (let ((rt (reform-T (ty-of st) s^))
                      (ra (reform-a (a-of st) s^)))
                     (if (equal "err" ra)
                         nil
                         (funcall (lambda (TY)
                                    (cond ((equal TY "err" ) mzero)
                                          (T (let ((d^ (remove nil (normalize-d<s/t/a #'subsumed-d-pr/a? (remove nil ra)
                                                                                             (remove nil (normalize-d<s/t/a #'subsumed-d-pr/T? TY (remove nil nds) s^)) s^))))
                                               (multiple-value-bind (ab ds)
                                                 (check-a/t->disequality TY (remove nil ra) s^ d^)
                                                 (unit (make-st
                                                         (cons s^ (c-of st))
                                                         ds
                                                         TY
                                                         ab))))))) (remove nil rt))))))
          mzero))))

(defun mplus ($1 $2)   ;like appendo
  (cond
    ((null? $1) $2)
    ((functionp $1) (lambda () (mplus $2 (funcall $1))))
    (T (cons (car $1) (mplus (cdr $1) $2)))))

(defun bind ($ g) ;like append-map
  (cond
    ((null? $) mzero)
    ((functionp $) (lambda () (bind (funcall $) g)))
    (T (mplus (funcall g (car $)) (bind (cdr $) g)))))


(defun disj (g1 g2)
  (lambda (st)
    (mplus (funcall g1 st) (funcall g2 st))))



(defun conj (g1 g2)
  (lambda (st)
    (bind (funcall g1 st) g2)))

;;;;;;;;;;;;;;;;;;;;;;;;   core "si-kanren" stops   ;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;   Disequality Constraint Store   ;;;;;;;;;;;;;;;;;;;;;;

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

(defun disequality (u v s st)
  (declare (ignore st))
  (let ((s^ (unify u v s)))
      (if (equal s^ '(()))
          '(())
          (let ((d (subtract-s s^ s)))
           (if (null? d)
            '()
             d)))))

(defun =/= (u v)
  (lambda (st)
    (let ((d^ (disequality u v (s-of st) st)))
      (if d^
          (if (equal d^ '(()))
              (unit st)
              (unit (make-st
                          (cons (s-of st) (c-of st))
                          (remove nil (normalize-d<s/t/a #'subsumed-d-pr/a? (a-of st)
                                                 (remove nil (normalize-d<s/t/a #'subsumed-d-pr/T? (ty-of st) (cons d^ (d-of st))(s-of st)))(s-of st)))
                          (ty-of st)
                          (a-of st))))
       mzero))))

(defun normalize-d<s/t/a (f s ds st)
 (bind (mapm (lambda (es)
               (let ((d^ (funcall f (mapcar #'car es)
                                    (mapcar #'cdr es)
                                    s
                                    st)))
                  (if d^
                      (if (equal d^ '(()))
                          '(())
                          (unit d^))
                      '(err))))
             (filter (lambda (l) (not (null? l)))
                     ds))
       (lambda (d)
         d)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;   Type Constraint Store     ;;;;;;;;;;;;;;;;;;;;;;

(defun tag=? (t0 t1)
  (eq t0 t1))

(defun tag-of (ty)
  (cadr ty))

(defun pred-of (ty)
   (cddr ty))

(defun ty-merge (a b)
    "Merge two type constraints for the *same* lvar.
     Returns either a merged entry or \"err\" if incompatible."
      (cond
            ((null a) b)
                ((null b) a)
                    ((equal (tag-of a) (tag-of b)) a)
                        (t "err")))

(defun tag? (tag)
  (symbolp tag))

(defun reform-T (TY S)
  "Canonicalize + check the type store TY under substitution S.

Returns:
  - a normalized TY list (possibly empty)
  - the string \"err\" if a constraint is violated or conflicts arise

A TY entry is (lvar . (tag . pred)) i.e. (x tag . pred)."
  (labels ((merge-entry (existing tag pred)
             ;; existing is (x tag0 . pred0)
             ;; Compatible only if tag matches.
             (if (tag=? (tag-of existing) tag)
                 existing
                 "err")))
    (let ((out '()))
      (dolist (e TY (nreverse out))
        (let* ((x    (car e))
               (tag  (tag-of e))
               (pred (pred-of e))
               (x*   (walk x S)))
          (cond
            ;; still a logic var → keep/merge on representative
            ((lvar? x*)
             (let ((old (assoc x* out :test #'equalp)))
               (if (null old)
                   (push (cons x* (cons tag pred)) out)
                   (let ((m (merge-entry old tag pred)))
                     (if (stringp m) ; "err"
                         (return-from reform-T "err")
                         ;; keep store clean: replace old with merged
                         (setf out (cons m (remove old out :test #'eq))))))))
            ;; ground term → must satisfy pred, then drop constraint
            (t
             (unless (funcall pred x*)
               (return-from reform-T "err")))))))))

(defun ty-add (TY S x tag pred)
  "Add the constraint (x : tag/pred) into TY under substitution S.

Returns:
  - normalized TY (via reform-T)
  - \"err\" on conflict/violation."
  (let ((x* (walk x S)))
    (cond
      ;; ground term: check now, TY unchanged if ok (but still canonicalize)
      ((not (lvar? x*))
       (if (funcall pred x*)
           (reform-T TY S)
           "err"))
      ;; logic var: extend then canonicalize/merge/alias-fix
      (t
       (reform-T (cons (cons x* (cons tag pred)) TY) S)))))

(defun typeo (tag pred x)
  "Generic type constraint goal."
  (lambda (st)
    (let* ((S  (S-of st))
           (x* (walk x S)))
      (cond
        ;; x is a logic var: add/merge type constraint, then normalize D and check A<->D
        ((lvar? x*)
         (let ((TY2 (ty-add (TY-of st) S x* tag pred)))
           (if (stringp TY2) ; \"err\"
               mzero
               (let* ((d2 (remove nil
                                  (normalize-d<s/t/a #'subsumed-d-pr/T?
                                                     TY2
                                                     (D-of st)
                                                     S))))
                 (multiple-value-bind (ab ds)
                     (check-a/t->disequality TY2 (a-of st) S d2)
                   (unit (make-st (S/C-of st) ds TY2 ab)))))))
        ;; x is ground: just check predicate
        (t
         (if (funcall pred x*) (unit st) mzero))))))


(defun subsumed-d-pr/T? (u v TY S)
  "Given lists U and V (same length) representing a mini-store:
   ((u1 . v1) (u2 . v2) ...),
   return '(()) if the conjunction is impossible under the type store TY
   (therefore the disequality constraint is trivially satisfied).
   Otherwise return the (walked) mini-store as a proper list of cons pairs.

   NOTE: must NOT return (unit ...) here."
  (labels
      ((ty-entry (x) (and (lvar? x) (assoc x TY :test #'equalp)))

       (typed-var-allows-term? (x term)
         (let ((tx (ty-entry x)))
           (cond
             ((null tx) t) ; no constraint on x
             ((lvar? term)
              (let ((tt (ty-entry term)))
                (or (null tt)
                    (tag=? (tag-of tx) (tag-of tt))))) ; tags must match if both known
             (t
              (funcall (pred-of tx) term))))) ; ground term must satisfy pred

       (binding-possible? (a b)
         ;; Evaluate possibility of equality a=b under TY
         (cond
           ((lvar? a) (typed-var-allows-term? a b))
           ((lvar? b) (typed-var-allows-term? b a))
           (t (equalp a b))))) ; both ground: equality possible only if equal

    (let* ((u* (mapcar (lambda (x) (walk x S)) u))
           (v* (mapcar (lambda (x) (walk x S)) v))
           (pairs (mapcar #'cons u* v*)))
      (if (some (lambda (pr)
                  (not (binding-possible? (car pr) (cdr pr))))
                pairs)
          '(())
          pairs))))


(defun symbolo (u) (typeo 'sym #'symbolp u))
(defun numbero (u) (typeo 'num #'numberp u))

;;;;;;;;;;;;;;;;;;;;;;;   Absento Constraint Store   ;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-pred-A (tag)
  (lambda (x) (not (and (tag? x) (tag=? x tag)))))

(defun ext-A-with-pred (x tag pred s a)
  (cond ((null? a) `((,x . (,tag . ,pred))))
        ((equal a "err")
         "err")
        (T (let ((ac (car A)))
             (let ((a-tag (tag-of ac)))
               (cond ((equal (walk (car ac) s) x)
                      (if (tag=? a-tag tag)
                          '(())
                          (ext-A-with-pred x tag pred s (cdr a))))
                     (T (ext-A-with-pred x tag pred s (cdr a)))))))))

(defun ext-A (x tag s a)
  (cond ((null? a)
         (let ((pred (make-pred-A tag)))
           `((,x . (,tag . ,pred)))))
        ((equal a "err")
         nil)
        (T (let ((ac (car a))
                 (ad (cdr a)))
               (let ((a-tag (tag-of ac)))
                 (cond ((equal (walk (car ac) s) x)
                        (if (tag=? a-tag tag)
                            '(())
                            (ext-A x tag S ad)))
                       ((tag=? a-tag tag)
                        (let ((a-pred (pred-of ac)))
                          (ext-A-with-pred x tag a-pred s ad)))
                       (T (ext-A x tag s ad))))))))

(defun subsumed-d-pr/A? (u v A S)
  "Given lists U and V (same length) representing a mini-store of equalities
   ((u1 . v1) (u2 . v2) ...),
   return '(()) if the conjunction is impossible under the absento store A
   (therefore the disequality constraint is trivially satisfied).
   Otherwise return the (walked) mini-store as a proper list of cons pairs.

   IMPORTANT: must NOT return (unit ...) here."
  (labels
      ((a-entries-for (x)
         ;; All absento constraints for logic var x (after walking keys through S).
         (let ((x* (walk x S)))
           (and (lvar? x*)
                (remove-if-not
                 (lambda (e) (equalp (walk (car e) S) x*))
                 (walk* A S)))))

       (absento-violated? (entry term)
         ;; entry is (x . (tag . pred)), term is the value x is forced equal to.
         (let* ((t*   (walk term S))
                (pred (pred-of entry)))
           ;; If pred says "allowed?", then violation is (not (pred t*))
           (and pred (not (funcall pred t*)))))

       (binding-impossible? (a b)
         ;; a=b required by the mini-store; decide if absento makes it impossible.
         (let ((a* (walk a S))
               (b* (walk b S)))
           (cond
             ;; If both are ground and unequal, equality can't ever hold → impossible
             ((and (not (lvar? a*)) (not (lvar? b*))
                   (not (equalp a* b*)))
              t)

             ;; If a is a constrained lvar and b is ground-ish: check absento violations
             ((lvar? a*)
              (let ((ents (a-entries-for a*)))
                (and ents
                     (not (lvar? b*))
                     (some (lambda (e) (absento-violated? e b*)) ents))))

             ;; Symmetric case
             ((lvar? b*)
              (let ((ents (a-entries-for b*)))
                (and ents
                     (not (lvar? a*))
                     (some (lambda (e) (absento-violated? e a*)) ents))))

             ;; If both are lvars, absento alone doesn't make equality impossible
             (t nil)))))

    (let* ((u* (mapcar (lambda (x) (walk x S)) u))
           (v* (mapcar (lambda (x) (walk x S)) v))
           (pairs (mapcar #'cons u* v*)))
      (if (some (lambda (pr) (binding-impossible? (car pr) (cdr pr))) pairs)
          '(())
          pairs))))


(defun absento/u (u tag st s/c d ty a)
  (let ((u (walk u (s-of st))))
    (cond ((lvar? u) (let ((A+ (ext-A u tag (s-of st) a)))
                       (cond ((null? A+) st)
                             (T (let ((d^ (remove nil (normalize-d<s/t/a #'subsumed-d-pr/a? (append A+ a) d (s-of st)))))
                                 (multiple-value-bind (ab ds)
                                   (check-a/t->disequality (remove nil ty) (append A+ a) (s-of st) d^)
                                   (make-st
                                             s/c
                                             ds
                                             ty
                                             ab)))))))
          ((pair? u) (let ((au (car u))
                           (du (cdr u)))
                       (let ((st (absento/u au tag st s/c d ty a)))
                         (and st (let ((s/c (s/c-of st))
                                       (d (d-of st))
                                       (ty (ty-of st))
                                       (a (remove nil (a-of st))))
                                   (absento/u du tag st s/c d ty a))))))
          (T (cond ((and (tag? u) (tag=? u tag)) nil)
                   (T st))))))

(defun absento (tag u)
  (cond ((not (tag? tag))
         (error "Incorrect absento usage: ~s is not a tag" tag))
        (T (lambda (st)
             (let ((s/c (s/c-of st))
                   (d (d-of st))
                   (ty (ty-of st))
                   (a (a-of st)))
                (let ((absu (absento/u u tag st s/c d ty a)))
                    (if absu
                        (unit absu)
                        mzero)))))))

(defun reform-A (A S)
  (cond ((null? A) '(()))
        ((let ((ra (reform-A (cdr A) S)))
          (if (equal ra "err")
              "err"
              (funcall (reform-A+ (car (car A)) A S) ra))))
        (T "err")))

(defun reform-A+ (x A S)
  (lambda (aol)
    (if (not (equal aol "err"))
        (let ((u (walk x S))
              (tag (tag-of (car A)))
              (pred (pred-of (car A))))
            (cond
                  ((not (or (lvar? u) (pair? u)))
                   "err")
                  ((equal u nil) nil)
                  ((lvar? u)
                   (let ((exa (ext-A-with-pred x tag pred S aol)))
                       (if (and exa (not (equal exa "err")))
                           (funcall (lambda (A+) (append A+ aol)) exa)
                           "err")))
                  ((pair? u)
                   (let ((au (car u))
                         (du (cdr u)))
                        (let ((ra+ (funcall (reform-A+ au A S) aol)))
                         (if (and ra+ (not (equal ra+ '(()))))
                             (funcall (reform-A+ du A S) ra+)
                             "err"))))
                  (T (and (funcall pred u) aol))))
        "err")))

;;; To check for disequality comparing the absento and the type stores
(defun check-a/t->disequality (ty ab s ds)
          (let ((seen '())
                (ab^ '()))
            (if (null? ab)
                (unit ds)
                (if (null? ty)
                    (progn
                      (setq ab^ ab)
                      (unit ds))
                    (mapcan (lambda (x)
                              (mapcar (lambda (a)
                                        (let ((u (walk* (car a) s))
                                              (v (walk* (car x) s)))
                                            (if (or (lvar=? u (car x))
                                                    (lvar=? u v))
                                                (if (funcall (pred-of x) (tag-of a))
                                                    (if (null? seen)
                                                        (progn (setq ds (cons (unit (cons u (tag-of a))) ds))
                                                               (setq seen (cons a seen))
                                                               (setq ab^ (remove a ab^ :test #'(lambda (l1 l2) (if (and (equalp (car l1) (car l2)) (equal (cadr l1) (cadr l2))) t nil)))))
                                                        (if (member a seen :test #'(lambda (l1 l2) (if (and (equalp (car l1) (car l2)) (equal (cadr l1) (cadr l2))) t nil)))
                                                            nil
                                                            (progn (setq ds (cons (unit (cons u (tag-of a))) ds))
                                                                   (setq seen (cons a seen))
                                                                   (setq ab^ (remove a ab^ :test #'(lambda (l1 l2) (if (and (equalp (car l1) (car l2)) (equal (cadr l1) (cadr l2))) t nil)))))))
                                                    (if (null? seen)
                                                        (progn (setq seen (cons a seen))
                                                               (setq ab^ (remove a ab^ :test #'(lambda (l1 l2) (if (and (equalp (car l1) (car l2)) (equal (cadr l1) (cadr l2))) t nil)))))
                                                        (if (member a seen :test #'(lambda (l1 l2) (if (and (equalp (car l1) (car l2)) (equal (cadr l1) (cadr l2))) t nil)))
                                                            nil
                                                            (progn (setq seen (cons a seen))
                                                                   (setq ab^ (remove a ab^ :test #'(lambda (l1 l2) (if (and (equalp (car l1) (car l2)) (equal (cadr l1) (cadr l2))) t nil))))))))
                                                (if (member a seen :test #'(lambda (l1 l2) (if (and (equalp (car l1) (car l2)) (equal (cadr l1) (cadr l2))) t nil)))
                                                    nil
                                                    (setq ab^ (cons a ab^)))))) (remove nil ab))) ty))) (values (remove-duplicates ab^ :test #'(lambda (l1 l2) (if (and (equalp (car l1) (car l2)) (equal (cadr l1) (cadr l2))) t nil))) ds)))
