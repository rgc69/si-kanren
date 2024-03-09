(in-package :si-kanren)

(defun make-st (S/C D TY A)
  `(,S/C ,D ,TY ,A))

(defun  empty-state () (make-st   '(() . 0) '() '() '()))

(defun S/C-of (st)
  (car st))

(defun S-of (st)
  (caar st))

(defun C-of (st)
  (cdar st))

(defun D-of (st)
  (cadr st))

(defun TY-of (st)
  (caddr st))

(defun a-of (st)
  (cadddr st))

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

(defun reify-state/1st-var (st)
  (let ((at (append (if (null? (a-of st)) '() `((absento . ,(a-of st)))) (ty-of st))))
   (labels (( o (ti)
             (let ((v (walk* ti (s-of st))))
                 (walk* v (reify-s v '())))))
    (o (cons (lvar 0)
         (cond
              ((and  (null? (d-of st)) (null? at))
               '())
              ((null? (d-of st))
               `(with ,at))
              ((null? at)
               `(where  ,(mapcar (lambda (mini) `,(if (equal (cdar mini) nil) ;If it's not a "composite" disequality, i.e. (=/= `(,x 9) `(3 ,y))
                                                      `,(if (cdr mini) ;If there are many disequalities
                                                            `(or . ,(mapcar (lambda (mini) (if (null (cdar mini))
                                                                                            `(=/= ,(car mini) ,(cdar mini))
                                                                                            (remove nil `(=/= ,(car mini) ,(cdr mini))))) mini))
                                                            (mapcar (lambda (mini) (if (null (cdar mini)) ;Otherwise, keep it simple
                                                                                       `(=/= ,(car mini) ,(cdar mini))
                                                                                       (remove nil `(=/= ,(car mini) ,(cdr mini))))) mini))
                                                      `(and . ,(mapcar (lambda (dis) (unit (remove nil `(=/= ,(car dis) ,(flatten (cdr dis)))))) mini))))
                              (d-of st))))
              ((and (d-of st) at)
               (cons `(where  ,(mapcar (lambda (mini) `,(if (equal (cdar mini) nil)
                                                          `,(if (cdr mini)
                                                                `(or . ,(mapcar (lambda (mini) (if (null (cdar mini))
                                                                                                `(=/= ,(car mini) ,(cdar mini))
                                                                                                (remove nil `(=/= ,(car mini) ,(cdr mini))))) mini))
                                                                (mapcar (lambda (mini) (if (null (cdar mini))
                                                                                           `(=/= ,(car mini) ,(cdar mini))
                                                                                           (remove nil `(=/= ,(car mini) ,(cdr mini))))) mini))
                                                            `(and . ,(mapcar (lambda (dis) (unit (remove nil `(=/= ,(car dis) ,(flatten (cdr dis)))))) mini))))
                                    (d-of st))) `(with ,at)))
              (T nil)))))))

(defun mK-reify (st)
    (if (equal nil st)
        nil)
    (let ((S (map 'list #'reify-state/1st-var st)))
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
  `(let ((st (runno ,num (,@queries) ,@goals)))
    (if (null st)
        nil
        (mK-reify (normalize-conde st)))))

(defmacro runno* ((&rest queries) &body goals)
  (let ((q (gensym)))
    `(take-all
        (call/empty-state
                   (fresh (,q ,@queries)
                          (conj+
                            (== `(,,@queries) ,q)
                            ,@goals))))))

(defmacro run* ((&rest queries) &body goals)
  `(let ((st (runno* (,@queries) ,@goals)))
    (if (null st)
        nil
        (mK-reify (normalize-conde st)))))

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
  (let ((seen '())
        (d^ '()))
    (mapcar (lambda (x)
              (if (null? seen)
                  (progn (setq seen (cons (car x) seen))
                         (setq d^ (cons x d^)))
                  (if (cdr x)
                      (setq d^ (cons x d^))
                      (if (member (car x) seen :test #'equal-lists)
                          '()
                          (progn
                            (setq seen (append x seen))
                            (setq d^ (cons x d^))))))) d) d^))

        ;;;;;;;;;;;;;   Getting rid of "ghost" vars ;;;;;;;;;;;;;;;;;

(defun walk-queries (n st)
  (labels ((walk-q (s)
             (if (null s)
                 '()
                 (if (lvar=? (lvar n) (caar s))
                     (car s)
                     (walk-q (cdr s))))))
   (let ((s^ (caaar st)))
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
        (apply 'concatenate 'list d))

(defun member-nested (el l)
  "whether el is a member of l, el can be atom or cons,
   l can be list of atoms or not"
      (cond
       ((null l) nil)
       ((dotted-pair-p l)
        (if (or (equalp el (car l)) (equalp el (cdr l)))
            t))
            ;(member-nested el (cddr l))))
       ((equalp el (car l)) t)
       ((consp (car l)) (or (member-nested el (car l))
                            (member-nested el (cdr l))))
       (t (member-nested el (cdr l)))))

;;; Normalize-fresh, together with norm=lvars, is used to normalize the
;;; disequality store, manteining the original structure, so that
;;; we can pass it to REIFY-STATE/1ST-VAR for a prettier reification
(defun normalize-fresh (st)
      (let ((d^ (flat-d (remove-subsumed (cadar st)))))
        (labels ((norm (d)
                  (if (null d)
                      '()
                      (if (and (not (member 't (flatten (mapcar (lambda (x) (lvar-or-atom (caar d) (walk* x (caaar st)))) (cdr (walk-queries 0 st))))))
                              (not (member 't (flatten (mapcar (lambda (x) (member-nested (caar d) (walk* x (caaar st)))) (cdr (walk-queries 0 st)))))))
                          (norm (cdr d))
                          (if (unused (car d) st)
                              (norm (cdr d))
                              (setq d (cons (car d)(norm (cdr d)))))))))
                (remove nil (mapcar #'norm d^)))))

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

(defun normalize-TY (st)
      (labels ((norm (l ty)
                 (if (null ty)
                     '()
                     (if (and (not (member 't (flatten (mapcar (lambda (x) (lvar-or-atom (caar ty) (walk* x (caaar l)))) (cdr (walk-queries 0 l))))))
                             (not (member 't (mapcar (lambda (x) (member-nested (caar ty) (walk* x (caaar l)))) (cdr (walk-queries 0 l))))))
                         (norm l (cdr ty))
                         (cons (car ty)(norm l (cdr ty)))))))
              (norm st (caddar st))))

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

;;;Only relevant values in the absento store, connected with main variables in S
(defun normalize-A (st)
      (labels ((norm (l ab)
                  (if (null ab)
                      '()
                      (if (member 't
                             (flatten (mapcar (lambda (x)
                                                (mapcar (lambda (s)
                                                          (if (and (member x (flatten s) :test #'equalp)
                                                                   (or (member (caar ab) (flatten s) :test #'equalp)
                                                                       (member (walk* (caar ab) (car (s-of l))) (flatten s) :test #'equalp)))
                                                           t
                                                           nil))(car (s-of l)))) (cdr (walk-queries 0 l)))))
                          (cons (car ab) (norm l (cdr ab)))
                          (norm l (cdr ab))))))
              (norm st (car (cdddar st)))))

(defun v>l (l) (cons (car l) (coerce->l (cadr l))))

(defun l>v (l) (cons (car l) (cons (coerce->v (cdr l)) nil)))

(defun part/A (A) (mapcar #'l>v (sort (mapcar #'v>l A) #'< :key #'cadr)))

;;;;;;;;;;;;;;;;;;;;;;;;;  Normalize everything  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun normalize (st)
  (if (not (cdr st))
      (norm=lvars (normalize-fresh st))
      (norm=lvars (normalize-fresh (cons (car st) nil)))))

(defun normalize-conde (st)
  (if (null st)
      '()
      (cons (make-st (caar st)
                     (let ((d (normalize st)))
                       (if (null? d)
                           nil
                           (unit d)))
                     (mapcar #'sort-part (partition* (drop-pred-t/a (normalize-ty st))))
                     (part/A (drop-pred-t/a (normalize-a st))))
           (normalize-conde (cdr st)))))
