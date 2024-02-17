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
                     (if (member '(err) ra)
                         nil
                         (funcall (lambda (TY)
                                    (cond ((member '(err) TY :test #'equal ) mzero)
                                          (T (let ((d^ (remove nil (normalize-d<s/t/a #'subsumed-d-pr/a? (remove nil ra)
                                                                                             (remove nil (normalize-d<s/t/a #'subsumed-d-pr/T? TY (remove nil nds) s^)) s^))))
                                               (multiple-value-bind (ab ds)
                                                 (post==-a<t>d/a ty (remove nil ra) s^ d^)
                                                 (unit (make-st
                                                         (cons s^ (c-of st))
                                                         ds
                                                         ty
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

(defun tag? (tag)
  (symbolp tag))

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
               ((tag=? t-tag tag) "same")
               ; Is it conflicting with the new constraint? Then fail.
               (T '((error)))))
             ; The current constraint is not on x, continue going through
             ; rest of the constraints
           (T (ext-TY x tag pred TY-next))))))))

(defun reform-T (TY S) ;; after a new symbolo/numbero declaration
  (cond ((null? TY) '())
        (T (let ((rt (reform-T (cdr TY) S)))
             (funcall (lambda (T0)
                        (let ((u (walk (car (car TY)) S))
                              (tag (tag-of (car TY)))
                              (pred (pred-of (car TY))))
                          (cond ((lvar? u)
                                 (cond ((let ((et (ext-TY u tag pred T0)))
                                         (cond ((equal et "err") mzero)
                                               ((equal et "same") rt)
                                               (T (funcall (lambda (T+) (append T+ T0)) et)))))
                                       (T "err")))
                                (T (if (or (funcall pred  u) rt)
                                       (append rt '(()))
                                       (append rt '((err)))))))) rt)))))

(defun subsumed-d-pr/T? (u v TY st)
      (cond
         ((cadr v)
          (let ((d (list (cons (car u) (car v)) (cons (cadr u) (cadr v)))))
           (cond
             ((and (lvar? (car u)) (lvar? (cadr u))(lvar? (car v))(lvar? (cadr v)))
              (let ((sc^ (assoc (car u) TY :test #'equalp)) ;;4 lvars
                    (sc^^ (assoc (cadr u) TY :test #'equalp))
                    (sc^^^ (assoc (car v) TY :test #'equalp))
                    (sc^^^^ (assoc (cadr v) TY :test #'equalp)))
                (if (and (not (null? (tag-of sc^^))) (not (null? (tag-of sc^^^^))))
                    (if (not (equal (tag-of sc^^) (tag-of sc^^^^)))
                        '(())
                        (if (and (not (null? (tag-of sc^))) (not (null? (tag-of sc^^^))))
                            (if (not (equal (tag-of sc^) (tag-of sc^^^)))
                                '(())
                                d)
                            d))
                    (if (and (not (null? (tag-of sc^))) (not (null? (tag-of sc^^^))))
                        (if (not (equal (tag-of sc^) (tag-of sc^^^)))
                            '(())
                            d)
                      d))))
             ((and (not (lvar? (car v)))(not (lvar? (cadr v))));2 lvars a sx
              (let ((sc^ (assoc (car u) TY :test #'equalp))
                    (sc^^ (assoc (cadr u) TY :test #'equalp))
                    (d (list (cons (car u)(car v))(cons (cadr u)(cadr v)))))
                (if (not (null? (tag-of sc^)))
                    (if (funcall (pred-of sc^) (car v))
                        (if (not (null? (tag-of sc^^)))
                            (if (funcall (pred-of sc^^) (cadr v))
                                d
                                '(()))
                            d)
                        '(()))
                    (if (not (null? (tag-of sc^^)))
                        (if (funcall (pred-of sc^^) (cadr v))
                            d
                            '(()))
                      d))))
             ((and (not (lvar? (car u)))(not (lvar? (cadr u))));2 lvars a dx
              (let ((sc^ (assoc (car v) TY :test #'equalp))
                    (sc^^ (assoc (cadr v) TY :test #'equalp))
                    (d (list (cons (car u)(car v))(cons (cadr u)(cadr v)))))
                (if (not (null? (tag-of sc^)))
                    (if (funcall (pred-of sc^) (car u))
                        (if (not (null? (tag-of sc^^)))
                            (if (funcall (pred-of sc^^) (cadr u))
                                d
                                '(()))
                            d)
                        '(()))
                    (if (not (null? (tag-of sc^^)))
                        (if (funcall (pred-of sc^^) (cadr u))
                            d
                            '(()))
                      d))))
             ((not (lvar? (cadr v)))
              (let ((sc^ (assoc (cadr u) TY :test #'equalp))
                    (sc^^ (assoc (car u) TY :test #'equalp))
                    (sc^^^ (assoc (car v) TY :test #'equalp))
                    (d (list (cons (car u)(car v))(cons (cadr u)(cadr v)))))
                (if sc^
                    (if (not (funcall (pred-of sc^) (cadr v)))
                        '(())
                         (if (and (not (null? (tag-of sc^^))) (not (null? (tag-of sc^^^))))
                             (if (not (equal (tag-of sc^^) (tag-of sc^^^)))
                                 '(())
                                 d)
                             d))
                    (if (and (not (null? (tag-of sc^^))) (not (null? (tag-of sc^^^))))
                        (if (not (equal (tag-of sc^^) (tag-of sc^^^)))
                            '(())
                            d)
                        d))))
             ((not (lvar? (car v)))
              (let ((sc^ (assoc (car u) TY :test #'equalp))
                    (sc^^ (assoc (cadr u) TY :test #'equalp))
                    (sc^^^ (assoc (cadr v) TY :test #'equalp))
                    (d (list (cons (car u)(car v))(cons (cadr u)(cadr v)))))
                (if sc^
                    (if (not (funcall (pred-of sc^) (car v)))
                        '(())
                         (if (and (not (null? (tag-of sc^^))) (not (null? (tag-of sc^^^))))
                             (if (not (equal (tag-of sc^^) (tag-of sc^^^)))
                                 '(())
                                 d)
                             d))
                    (if (and (not (null? (tag-of sc^^))) (not (null? (tag-of sc^^^))))
                        (if (not (equal (tag-of sc^^) (tag-of sc^^^)))
                            '(())
                            d)
                        d))))
             (T (or (lvar? (cadr u)) (lvar? (cadr v)));1 lvar a dx di u, 1 a sx di v
                (if (lvar? (cadr v))
                    (let ((sc^ (assoc (car u) TY :test #'equalp)))
                         (if sc^
                             (if (not (funcall (pred-of sc^) (car v)))
                               '(())
                                d)
                             d))
                    (let ((sc^^ (assoc (cadr u) TY :test #'equalp)))
                     (if sc^^
                         (if (not (funcall (pred-of sc^^) (cadr v)))
                           '(())
                            d)
                         d)))))))
         ((lvar? (car v))
          (let ((sc^ (assoc (car u) TY :test #'equalp))
                (sc^^ (assoc (car v) TY :test #'equalp))
                (d (list(cons (car u) (car v)))))
              (if (and sc^ sc^^)
                  (if (equal (tag-of sc^)(tag-of sc^^))
                      d
                      '(()))
                  d)))
         (T (let ((sc^ (assoc  (car u) TY :test #'equalp))
                  (d^ (cons (car u) (car v))))
              (if sc^
                  (if (not (funcall (pred-of sc^) (car v)))
                      '(())
                      (unit d^))
                  (unit d^))))))

(defun make-type-constraint/x (u tag pred st)
     (let ((ty (ext-TY u tag pred (ty-of st))))
          (funcall (lambda (T+)
                     (cond ((equal T+ "same") st)
                           ((equal T+ '((error))) '())
                           (T (let ((d (remove nil (normalize-d<s/t/a #'subsumed-d-pr/T? (cons (car T+) (ty-of st)) (d-of st)(s-of st)))))
                                  (type->diseq T+ (a-of st) d st '() '() (ty-of st)))))) ty)))

(defun type->diseq (ty+ a d s d+ a+ ty);for a new type, after an absento constraint
  (if (null? a)
      (if (null? d)
          (make-st (s/c-of s) (remove nil d+) (cons (car ty+) ty) a+)
          (make-st (s/c-of s) (apply 'concatenate 'list(list d d+)) (cons (car ty+) ty) a+))
      (if (lvar=? (caar ty+) (walk* (caar a) (s-of s)))
          (if (funcall (pred-of (car ty+)) (tag-of (car a)))
              (let ((d^ (list (unit (cons (caar ty+)(tag-of (car a)))) d+)))
                 (type->diseq ty+ (cdr a) d s d^ a+ ty))
              (type->diseq ty+ (cdr a) d s d+ a+ ty))
          (let ((a^ (cons (car a) a+)))
            (type->diseq ty+ (cdr a) d s d+ a^ ty)))))

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

(defun symbolo (u) (funcall (make-type-constraint 'sym #'symbolp) u))

(defun numbero (u) (funcall (make-type-constraint 'num #'numberp) u))

;;;;;;;;;;;;;;;;;;;;;;;   Absento Constraint Store   ;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-pred-A (tag)
  (lambda (x) (not (and (tag? x) (tag=? x tag)))))

(defun ext-A-with-pred (x tag pred s a)
  (cond ((null? a) `((,x . (,tag . ,pred))))
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
      (cond
         ((cdr u)
          (let ((sc^ (assoc (car u) (walk* A S) :test #'equalp))
                (sc^^ (assoc (cadr u) (walk* A S) :test #'equalp))
                (d (list (cons (car u) (car v)) (cons (cadr u) (cadr v)))))
             (if (or sc^ sc^^)
                (if sc^
                    (if (tag=? (tag-of sc^) (car v))
                     '(())
                     d)
                    (if sc^^
                        (if (tag=? (tag-of sc^^) (cadr v))
                           '(())
                            d)))
                d)))
         ((lvar? (car v))
          (let ((sc^ (assoc (car u) A :test #'equalp))
                (sc^^ (assoc (car v) A :test #'equalp))
                (d (list(cons (car u) (car v)))))
              (if (and sc^ sc^^)
                  (if (equal (tag-of sc^)(tag-of sc^^))
                      d
                      '(()))
                  d)))
         (T (let ((sc (assoc  (car u) (walk* A S) :test #'equalp))
                  (d^ (cons (car u) (car v))))
              (if sc
                  (if (tag=? (tag-of sc) (car v))
                      '(())
                      (unit d^))
                  (unit d^))))))

(defun absento/u (u tag st s/c d ty a)
  (let ((u (walk u (s-of st))))
    (cond ((lvar? u) (let ((A+ (ext-A u tag (s-of st) a)))
                       (cond ((null? A+) st)
                             (T (let ((d (remove nil (normalize-d<s/t/a #'subsumed-d-pr/a? A+ (d-of st) (s-of st)))))
                                  (absento->diseq A+ s/c d ty a))))))
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

(defun absento->diseq (a+ s/c d ty a)
  (cond ((null? ty)
         (let ((a^ (append a+ a)))
           (make-st s/c d ty (remove nil a^))))
        (T (let ((d/a (absento->diseq/x (car s/c) d ty a+)))
             (if (equal d/a 'rem)
                 (make-st s/c d ty a)
                 (let ((d (car d/a))
                       (a+ (cdr d/a)))
                   (make-st s/c d ty (remove nil (append a+ a)))))))))

(defun absento->diseq/x (s d ty a+)
  (cond ((null? ty)
         `(,d . ,a+))
        (T (let ((ty* (car ty)))
                (if (caar a+)
                    (if (lvar=? (car ty*) (walk* (caar a+) s))
                        (if (funcall (pred-of ty*) (tag-of a+))
                            (absento->diseq/x+ (caar a+) '() s d a+)
                            'rem)
                        (absento->diseq/x s d (cdr ty) a+))
                    (absento->diseq/x s d (cdr ty) a+))))))


(defun absento->diseq/x+ (x a+ s d a)
  (cond ((null? A)
         `(,d . ,a+))
        (T (let ((ac (car a))
                 (ad (cdr a)))
                (let ((d* (ext-D x (tag-of ac) d s)))
                  (absento->diseq/x+ x a+ s d* ad))))))

(defun ext-D (x tag d s)
  (cond ((find-if (lambda (d) (and (null? (cdr d))
                                   (let ((d-ca (car (car d)))
                                         (d-cd (cdr (car d))))
                                     (and (equalp (walk d-ca s) x)
                                          (tag? d-cd)
                                          (tag=? d-cd tag))))) d)
         d)
        (T (cons `((,x . ,tag)) d))))

(defun reform-A (A S)
  (cond ((null? A) '(()))
        ((let ((ra (reform-A (cdr A) S)))
          (funcall (reform-A+ (car (car A)) A S) ra)))
        (T '((err)))))

(defun reform-A+ (x A S)
  (lambda (aol)
    (let ((u (walk x S))
          (tag (tag-of (car A)))
          (pred (pred-of (car A))))
        (cond ((lvar? u)
               (let ((exa (ext-A-with-pred x tag pred S aol)))
                   (if exa
                       (funcall (lambda (A+) (append A+ aol)) exa)
                       '(err))))
              ((pair? u)
               (let ((au (car u))
                     (du (cdr u)))
                    (let ((ra+ (funcall (reform-A+ au A S) aol)))
                     (if ra+
                         (funcall (reform-A+ du A S) ra+)
                         '(err)))))
              (T (and (funcall pred u) aol))))))

;;; To check post-unification in the absento and type stores
(defun post==-a<t>d/a (ty ab s ds)
          (let ((seen '())
                (ab^ '()))
            (if (null? ab)
                (unit ds)
                (if (null? ty)
                    (progn
                      (unit ds)
                      (unit ab))
                    (mapcan (lambda (x)
                              (mapcar (lambda (a)
                                        (let ((u (walk* (car a) s))
                                              (v (walk* (car x) s)))
                                            (if (or (lvar=? u (car x))
                                                    (lvar=? u v))
                                                (if (funcall (pred-of x) (tag-of a))
                                                    (if (null? seen)
                                                        (progn (setq ds (cons (unit (cons (car a) (tag-of a))) ds))
                                                               (setq seen (cons a seen))
                                                               (setq ab^ (remove a ab^ :test #'(lambda (l1 l2) (if (and (equalp (car l1) (car l2)) (equal (cadr l1) (cadr l2))) t nil)))))
                                                        (if (member a seen :test #'(lambda (l1 l2) (if (and (equalp (car l1) (car l2)) (equal (cadr l1) (cadr l2))) t nil)))
                                                            nil
                                                            (progn (setq ds (cons (unit (cons (car a) (tag-of a))) ds))
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
                                                    (setq ab^ (cons a ab^)))))) ab)) ty))) (values (remove-duplicates ab^ :test #'(lambda (l1 l2) (if (and (equalp (car l1) (car l2)) (equal (cadr l1) (cadr l2))) t nil))) ds)))
