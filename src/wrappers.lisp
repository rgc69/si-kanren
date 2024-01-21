(in-package :si-kanren)

(defun make-st (S/C D TY A)
  `(,S/C ,D ,TY ,A))

(defun  empty-state () (make-st   '(() . 0) '() '() '()))

(defun S/C-of (s/c/d)
  (car s/c/d))

(defun S-of (s/c/d)
  (caar s/c/d))

(defun C-of (s/c/d)
  (cdar s/c/d))

(defun D-of (s/c/d)
  (cadr s/c/d))

(defun TY-of (s/c/d)
  (caddr s/c/d))

(defun a-of (s/c/d)
  (cadddr s/c/d))

(defun pull (st)
  (if (functionp st)
      (pull (funcall st))
      st))

(defun take (n st)
  (if (= 0 n) '()
      (let ((st (pull st)))
           (cond
                   ((null? st) '())
                   (t (cons (car st) (take (- n 1) (cdr st))))))))

(defun take-all (st)
  (let ((next (pull st)))
      (if (null? next)
          '()
           (cons (car next) (take-all (cdr next))))))

(defun call/empty-state (g)
  (funcall g (empty-state)))

(defun reify-s (v s)
  (let ((v (walk v s)))
      (cond
           ((lvar? v)
            (let ((n (reify-name (length s))))
                 (cons `(,v . ,n) s)))
           ((pair? v)
            (reify-s (cdr v) (reify-s (car v) s)))
           (t s))))

(defun reify-name (n)
  (make-symbol (concatenate 'string "_." (write-to-string n))))

(defun reify-state/1st-var (s/c/d)
  (let ((at (append (if (null? (a-of s/c/d)) '() `((absento . ,(a-of s/c/d)))) (ty-of s/c/d))))
   (labels (( o (ti)
             (let ((v (walk* ti (s-of s/c/d))))
                 (walk* v (reify-s v '())))))
    (o (cons (lvar 0)
         (cond
              ((and (null? (d-of s/c/d)) (null? at))
               nil)
              ((null? at)
               (if (not (equal (cdar (d-of s/c/d)) nil))
                   `(where ,(mapcar (lambda (mini) `(and . ,(mapcar (lambda (dis) `(=/= ,(car dis) ,(cdr dis))) mini)))
                               (cadr s/c/d)))
                   `(where  ,(mapcar (lambda (mini) `,(mapcar (lambda (dis) `(=/= ,(car dis) ,(cdr dis))) mini))
                                  (cadr s/c/d)))))
              ((null? (d-of s/c/d))
               `(with ,at))
              ((and (d-of s/c/d) at)
               (if (not (equal (cdar (d-of s/c/d)) nil))
                  (cons `(where  ,(mapcar (lambda (mini) `(and . ,(mapcar (lambda (dis) `(=/= ,(car dis) ,(cdr dis))) mini)))
                                   (cadr s/c/d))) `(with ,at))
                  (cons `(where  ,(mapcar (lambda (mini) `,(mapcar (lambda (dis) `(=/= ,(car dis) ,(cdr dis))) mini))
                                   (cadr s/c/d))) `(with ,at))))
              (T nil)))))))

(defun mK-reify (s/c/d)
    (if (equal nil s/c/d)
        nil)
     ;(if (cdr s/c/d)
         ;(setq s/c/d (mapcar (lambda (l) (remove nil l)) s/c/d))
         ;(setq s/c/d (cons (remove nil (car s/c/d)) '()))))
    (let ((S (apply 'concatenate 'list (map 'list #'reify-state/1st-var s/c/d))))
       (if (cdr S)
           (format t "~{~a~%~^ ~}" S)
           (format t "~{~a~^ ~}" (car S))))
    (values))

(defun walk* (v s)
  (let ((v (walk v s)))
      (cond
            ((lvar? v) v)
            ((pair? v)
             (cons (walk* (car v) s)
                   (walk* (cdr v) s)))
            (t v))))

(defmacro zzz (g)
  `(lambda (s/c) (lambda() (funcall ,g s/c))))

(defmacro conj+ (g &rest goals)
  (if goals
       `(conj (zzz ,g) (conj+ ,@goals))
       `(zzz ,g)))

(defmacro disj+ (g &rest goals)
  (if goals
       `(disj (zzz ,g) (disj+ ,@goals))
       `(zzz ,g)))


(defmacro conde (&rest clauses)
  `(symbol-macrolet ((else +succeed+))
    (disj+ ,@(loop for c in clauses collect `(conj+ ,@c)))))

(defmacro fresh (&rest e)
  (cond
      ((null? (car e)) `(conj+ ,@(cdr e)))
      (t `(call/fresh (lambda (,(car (car e)))
                            (fresh ,(cdr (car e)) ,@(cdr e)))))))

(defmacro runno (num (&rest queries) &body goals)
  (let ((q (gensym)))
    `(take ,num
              (call/empty-state
                         (fresh (,q ,@queries)
                                (conj+
                                  (== `(,,@queries) ,q)
                                  ,@goals))))))

(defmacro run (num (&rest queries) &body goals)
  `(let ((s/c/d (runno ,num (,@queries) ,@goals)))
    (if (null s/c/d)
        nil
        (mK-reify (normalize-conde s/c/d)))))

(defmacro runno* ((&rest queries) &body goals)
  (let ((q (gensym)))
    `(take-all
        (call/empty-state
                   (fresh (,q ,@queries)
                          (conj+
                            (== `(,,@queries) ,q)
                            ,@goals))))))

(defmacro run* ((&rest queries) &body goals)
  `(let ((s/c/d (runno* (,@queries) ,@goals)))
    (if (null s/c/d)
        nil
        (mK-reify (normalize-conde s/c/d)))))

(defmacro nlet-tail (n letargs &rest body)
      (let ((gs (loop for i in letargs
                  collect (gensym)))
            (gb (gensym))
            (gn (gensym)))
         `(macrolet
             ((,n ,gs
               `(progn
                  (psetq
                      ,@(apply #'nconc
                          (mapcar
                              #'list
                              ',(mapcar #'car letargs)
                              (list ,@gs))))
                  (go ,',gn))))
            (block ,gb
              (let ,letargs
                (tagbody
                  ,gn (return-from
                         ,gb (progn ,@body))))))))


(defmacro runi ((&rest queries) &body goals)
      `(let* (($ (runno* (,@queries) ,@goals))
              ($* (normalize-conde $)))
        (nlet-tail named-loop (($* (pull $*)))
           (if (equal $* '())
               (format t "thats-all!~%")
               (values (format t "~{~a~^ ~}~%" (reify-state/1st-var (car $*)))
                       (format t "another? y/n~%")
                       (case (read)
                         ((y yes) (named-loop (pull (cdr $*))))
                         (t (format nil "bye!"))))))))


;;;;;;;;;;;;;;;;;;;;    "Pars construens" of the Reifier     ;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;   Normalization of the Disequality Store ;;;;;;;;;;;;;;;;

  ;;;;;;;   Getting rid of constraints subsumed by others constraints  ;;;;;

(defun eigenvalue (v)
  (and (not (subsumed v)) (not (lvar? (cdr v)))))

(defun subsumed (v)
 (if (equal nil v)
     '()
     (if (consp (cdr v))
         t
         nil)))

(defun normalize-subsumed (tree)
   (let ((seen NIL)(lists-seen nil))
     (labels ((rec (l)
               (cond
                 ((null l) NIL)
                 ((member (car l) seen :test #'equal) (rec (cdr l)))
                 ((subsumed (car l))(push (car l) lists-seen)(rec (cdr l)))
                 (T (push (car l) seen) (rec (cdr l))))))
       (rec tree)
      (values seen
              lists-seen))))

(defun normalize-lists-seen (s ls)
  (if (equal nil ls)
      nil
      (if (member (car s) (car ls) :test #'equal-lists)
          (normalize-lists-seen s (cdr ls))
          (cons (car ls)(normalize-lists-seen s (cdr ls))))))

(defun remove-subsumed (d)
  (multiple-value-bind (seen ls-seen)
    (normalize-subsumed d)
    (mapcar (lambda (si) (setq ls-seen (normalize-lists-seen si ls-seen))) seen)
    (cons seen (cons ls-seen '()))))

     ;;;;;;;;   Getting rid of duplicates, in a "set theory" sense   ;;;;;;;;;

(defun norm-cons (xs)
 (if (not (consp (cdr xs)))
     (cons (car xs) (cons (cdr xs)'()))
     (cons (car xs) (norm-cons (cdr xs)))))

(defun dotted-pair-p (arg) (and (not (atom arg)) (not (listp (cdr arg)))))

(defun equal-lists (list1 list2)
  (if (dotted-pair-p list1)
   (and (eq (null (intersection (norm-cons list1) (norm-cons list2) :test #'equalp)) nil)
        (null (set-difference (norm-cons list1) (norm-cons list2) :test #'equalp)))
   '()))

(defun norm=lvars (d)
  (remove-duplicates d :test #'equal-lists))

        ;;;;;;;;;;;;;   Getting rid of "ghost" vars ;;;;;;;;;;;;;;;;;

(defun walk-queries (n s/c/d)
  (labels ((walk-q (s)
             (if (null s)
                 '()
                 (if (lvar=? (lvar n) (caar s))
                     (car s)
                     (walk-q (cdr s))))))
   (let ((s^ (caaar s/c/d)))
     (walk-q s^))))

(defun lvar-or-atom (v l)
  "T if v in walking l is another lvar"
  (if (lvar? l)
      (lvar=? v l)
      (if (not (consp l))
       '()
       (if (null l)
        '()
        (if (lvar? (car l))
            (cons (lvar=? v (car l)) (lvar-or-atom v (cdr l)))
            (lvar-or-atom v (cdr l)))))))

(defun flatten (x)
    (labels ((rec (x acc)
                (cond ((null x) acc)
                      ((typep x 'sb-impl::comma) (rec (sb-impl::comma-expr x) acc))
                      ((atom x) (cons x acc))
                      (t (rec
                            (car x)
                            (rec (cdr x) acc))))))
        (rec x nil)))

(defun flat-d (d)
         (apply 'concatenate 'list
                (apply 'concatenate 'list d)))

(defun normalize-fresh (s/c/d)
      (labels ((norm (l d)
                 (if (null d)
                     '()
                  (if (not (member 't (flatten (mapcar (lambda (x) (lvar-or-atom (caaar d) (walk* x (caaar l)))) (cdr (walk-queries 0 l))))))
                      (norm l (cdr d))
                      (if (unused (caar d) l)
                          (norm l (cdr d))
                          (cons (car d)(norm l (cdr d))))))))
        (let ((d^ (apply 'concatenate 'list (remove-subsumed (cadar s/c/d)))))
         (norm s/c/d d^))))

          ;;;;;;;;;;;   Getting rid of unused vars   ;;;;;;;;;;;;;

(defun unused (v l)
 (cond
   ((eigenvalue v) nil)
   ((symbolp (cdr v)) nil)
   ((listp (cdr v))(not (symbolp (cadr v))))
   ((member 't (flatten (mapcar (lambda (x) (lvar-or-atom (cdr v) (walk* x (caaar l)))) (cdr (walk-queries 0 l))))) nil)
   ((listp (cdr v))(not (member 't (flatten (mapcar (lambda (x) (lvar-or-atom (cadr v) (walk* x (caaar l)))) (cdr (walk-queries 0 l)))))))
   ((listp (cdr v))(lvar-or-atom (cadr v)(walk* (cadr v) (caaar l))))
   (T (lvar-or-atom (cdr v) (walk* (cdr v) (caaar l))))))

;;;;;;;;;;;;;;;;;;;;;;;; Normalization of the Type Store  ;;;;;;;;;;;;;;;;;;;;;

(defun normalize-TY (s/c/d)
      (labels ((norm (l ty)
                 (if (null ty)
                     '()
                     (if (not (member 't (flatten (mapcar (lambda (x) (lvar-or-atom (caar ty) (walk* x (caaar l)))) (cdr (walk-queries 0 l))))))
                         (norm l (cdr ty))
                         (cons (car ty)(norm l (cdr ty)))))))
              (norm s/c/d (caddar s/c/d))))

(defun drop-pred-T/A (TY) (mapcar (lambda (ty) (let ((x (car ty))
                                                     (tag (tag-of ty)))
                                                   `(,tag ,x))) TY))

(defun partition* (A)
  (cond ((null? A) '())
        (T (part (car (car A)) A '() '()))))

(defun part (tag A x* y*)
  (cond ((null? A) (cons `(,tag . ,(mapcar #'car x*)) (partition* y*)))
        ((tag=? (car (car A)) tag)
         (let ((x (cdr (car A))))
           (let ((x* (cond ((member x x*) x*)
                           (T (cons x x*)))))
             (part tag (cdr A) x* y*))))
        (T (let ((y* (cons (car A) y*)))
             (part tag (cdr A) x* y*)))))

(defun coerce->l (v) (coerce v 'list))

(defun coerce->v (l) (coerce l 'vector))

(defun sort-part (pr)
  (let ((tag (car pr))
        (x* (mapcar #'coerce->v
                    (mapcar #'unit
                            (sort (apply 'concatenate 'list
                                         (mapcar #'coerce->l (cdr pr))) #'<)))))
    `(,tag . ,x*)))

;;;;;;;;;;;;;;;;;;;;;;;; Normalization of the Absento Store  ;;;;;;;;;;;;;;;;;;;;;

(defun normalize-A (s/c/d)
      (labels ((norm (l a)
                 (if (null a)
                     '()
                     (if (not (member 't (flatten (mapcar (lambda (x) (lvar-or-atom (caar a) (walk* x (caaar l)))) (cdr (walk-queries 0 l))))))
                         (norm l (cdr a))
                         (cons (car a)(norm l (cdr a)))))))
              (norm s/c/d (car (cdddar s/c/d)))))

(defun v>l (l) (cons (car l) (coerce->l (cadr l))))

(defun l>v (l) (cons (car l) (cons (coerce->v (cdr l)) nil)))

(defun part/A (A) (mapcar #'l>v (sort (mapcar #'v>l A) #'< :key #'cadr)))

;;;;;;;;;;;;;;;;;;;;;;;;;  Normalize everything  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun normalize (s/c/d)
  (if (not (cdr s/c/d))
      (norm=lvars (normalize-fresh s/c/d))
      (norm=lvars (normalize-fresh (cons (car s/c/d) nil)))))

(defun normalize-conde (s/c/d)
  (if (null s/c/d)
      '()
      (cons (make-st (caar s/c/d)
                     (normalize s/c/d)
                     (mapcar #'sort-part (partition* (drop-pred-t/a (normalize-ty s/c/d))))
                     (part/A (drop-pred-t/a (normalize-a s/c/d))))
           (normalize-conde (cdr s/c/d)))))
