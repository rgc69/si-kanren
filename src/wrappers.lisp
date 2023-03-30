(in-package :si-kanren)

(defparameter empty-state '((() . 0) . ()))

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
  (funcall g empty-state))

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
  (labels (( o (ti)
            (let ((v (walk* ti (caar s/c/d))))
                (walk* v (reify-s v '())))))
   (o (cons (lvar 0)
        (if (and (not (equal (cdr s/c/d) '(())))
                 (not (equal (cdr s/c/d) '())))
            (if (or (cddr s/c/d)(cdadr s/c/d))
                `(where . ,(mapcar (lambda (mini) `(or . ,(mapcar (lambda (dis) `(=/= ,(car dis) ,(cdr dis))) mini)))
                                (cdr s/c/d)))
                `(where . ,(mapcar (lambda (mini) `,(mapcar (lambda (dis) `(=/= ,(car dis) ,(cdr dis))) mini))
                                (cdr s/c/d))))
            '())))))

(defun mK-reify (s/c/d)
    (if (equal nil s/c/d)
        nil
     (if (cdr s/c/d)
         (setq s/c/d (mapcar (lambda (l) (remove nil l)) s/c/d))
         (setq s/c/d (cons (remove nil (car s/c/d)) '()))))
    (let ((S (map 'list #'reify-state/1st-var s/c/d)))
       (if (cdr S)
           (format t "~{~a~%~^ ~}" S)
           (format t "~{~a~^ ~}" (car S)))))

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


(defmacro run (num (&rest queries) &body goals)
  `(multiple-value-bind (n s/c/d) (runno ,num (,@queries) ,@goals)
    (if (equal s/c/d nil)
        nil
        (let ((tot (cdaar s/c/d)))
          ;(if (fresh-search 0 (cdar s/c/d))
           (mK-reify (cons (cons (caar s/c/d) (norm (+ 3 n) tot (cdar s/c/d))) ()))))))
            ;nil)))))

(defmacro run* ((&rest queries) &body goals)
  `(multiple-value-bind (n s/c/d) (runno* (,@queries) ,@goals)
    (if (equal s/c/d nil)
        nil
        (let ((tot (cdaar s/c/d)))
         (mK-reify (cons (cons (caar s/c/d) (norm (+ 1 n) tot (cdar s/c/d))) ()))))))

(defmacro runno (num (&rest queries) &body goals)
  (let ((q (gensym)))
    `(values-list
       (append (multiple-value-list (length ',queries))
               (multiple-value-list (take ,num
                                            (call/empty-state
                                                       (fresh (,q ,@queries)
                                                              (conj+
                                                                (== `(,,@queries) ,q)
                                                                ,@goals)))))))))

(defmacro runno* ((&rest queries) &body goals)
  (let ((q (gensym)))
    `(values-list
      (append (multiple-value-list (length ',queries))
              (multiple-value-list (take-all
                                     (call/empty-state
                                                (fresh (,q ,@queries)
                                                       (conj+
                                                         (== `(,,@queries) ,q)
                                                         ,@goals)))))))))

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
  (let ((q (gensym)))
      `(let (($ (take-all
                      (call/empty-state
                                   (fresh (,q ,@queries)
                                          (conj+
                                            (== `(,,@queries) ,q)
                                            ,@goals))))))
        (nlet-tail named-loop (($ (pull $)))
           (if (equal $ '())
               (format t "thats-all!~%")
               (values (format t "~{~a~^ ~}~%" (reify-state/1st-var (car $)))
                       (format t "another? y/n~%")
                       (case (read)
                         ((y yes) (named-loop (pull (cdr $))))
                         (t (format nil "bye!")))))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun fresh-search (x l)
  (if (equal nil l)
      '()
      (if (lvar=? (lvar x) (caaar l))
          t
          (cons (car l)(fresh-search x (cdr l))))))

(defun normalize-fresh (x l)
  (if (equal nil l)
      '()
      (if (lvar=? (lvar x) (caaar l))
          (normalize-fresh x (cdr l))
          (cons (car l)(normalize-fresh x (cdr l))))))

(defun norm (n m l)
  (do ((cnt n (+ cnt 1))
       (z l))
      ((eq cnt m) z)
      (setq z (normalize-fresh cnt z))))

;(apply 'concatenate 'list ....) non va bene flatten

;(defun walk-vect (v d)
  ;(if (and (lvar? v)
           ;(pair? d)
           ;(the-pos v d)))

 ;(defun walk (u s)
       ;(walk (cdr (elt s (the-pos u s))) s)
       ;u))
