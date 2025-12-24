;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; TABLE OF CONTENTS
;;;   1) Small library (macros + basic relations) ................. [line ~15]
;;;   2) Playground: quick sanity-check queries ................... [line ~65]
;;;   3) Parents / grandparent / cousin relations ................. [line ~281]
;;;   4) Tiny taxonomy-style constraint demo ...................... [line ~346]
;;;   5) Zebra puzzle + “who owns the fish?” queries .............. [line ~375]
;;;   6) Interpreter v0 (minimal) — quines/twines demos ........... [line ~602]
;;;      - Quines & Twines ........................................ [line ~665]
;;;   7) Interpreter v1 (extended core) — letrec + primitives ......[line ~681]
;;;      - Unguided synthesis examples (holes, spurious possible) ..[line ~842]
;;;      - Guided synthesis helpers + examples (bounded, roles) ....[line ~862]
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;   A small library....   ;;;;;;;;;;;;;;;;;;;;;;;

(defmacro suspend (&rest body)
  `(lambda () ,@body))

(defmacro defrel ((name &rest args) &body body)
  (let ((s^ (gensym)))
     `(defun ,name  (,@args)
       (lambda (s^)
         (suspend
           (funcall (conj+ ,@body) s^))))))

(defun caro (p a)
  (fresh (d)
    (== (cons a d) p)))

(defun cdro (p d)
  (fresh (a)
    (== (cons a d) p)))

(defun membero (x l)
  (conde
   ((caro l x))
   ((fresh (d)
      (cdro l d)
      (membero x d)))))

(defun appendo (l s out)
 (conde
    ((== '() l) (== s out))
    ((fresh (a d res)
         (== `(,a . ,d) l)
         (== `(,a . ,res) out)
         (appendo d s res)))))

(defun conso (first rest out)
  (if (lvar? rest)
      (== `(,first . ,rest) out)
      (== (cons first rest) out)))

(defun fives (x)
  "inverse-n-delay"
    (disj (== x 5) (lambda (s/c) (lambda () (funcall (fives x) s/c)))))

(defun sixes (x)
    (disj (== x 6) (lambda (s/c) (lambda () (funcall (sixes x) s/c)))))

(defun fives-and-sixes ()
  (call/fresh (lambda (x) (disj (fives x) (sixes x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;  Playground  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+nil
(progn
  (run 1 (q)
         (fresh (x y)
            (== x 10)
            (=/= y 5)
            (=/=  y 2)
            (== y 9)
            (== q `(,x . ,y))))

  (run 1 (q) (fresh (x y z)
                    (=/= z 8)
                    (== x y)
                    (== x z)
                    (== 3 y)
                    (== q `(,x ,y ,z))))

  (run 1 (q) (fresh (x y z)
                    (=/= z 8)
                    (== x y)
                    (== x z)
                    (== 3 y)
                    (== 1 z)
                    (== q `(,x ,y ,z))))

  (run 5 (q)
    (fresh (x y z)
      (== x z)
      (== 3 y)
      (=/= z y)
      (== q `(,x ,y ,z))))

  (run 2 (q)
    (fresh (w x y)
      (conde
        ((== `(,x ,w ,x) q)
         (== y w))
        ((== `(,w ,x ,w) q)
         (== y w)))))

 (run* (x y) (== x 9) (== y 42))

 (run* (p) (=/= p 1))

 (run* (p) (=/= 1 p) (== 1 p))

  (run* (q)
    (fresh (p r)
      (=/= '(1 2) `(,p ,r))
      (== `(,p ,r) q)))

  (run* (q)
    (fresh (p r)
      (=/= '(1 2) `(,p ,r))
      (== 1 p)
      (== `(,p ,r) q)))

  (run* (q)
    (fresh (p r)
      (=/= '(1 2) `(,p ,r))
      (== r 2)
      (== 1 p)
      (== `(,p ,r) q)))

  (run* (q)
    (fresh (a b c)
          (disj+
             (== q 1)
             (== q 2)
             (== q 3))))

  (run 2 (q)
         (== 1 q)
         (== 1 1))

  (run* (r)
      (fresh (y x)
        (== `(,x ,y) r)))

  (run* (q)
    (== q (list 1 2 3)))

  (run* (r) (fresh (x y z)
                   (== `(e a d ,x) r)
                   (conso y `(a ,z c) r)))

  (run* (x) (conso x `(a ,x c) `(d a ,x c)))

  (run* (x) (conso x `(a ,x c) `(d a ,x d c)))

  (run 10 (q)
         (conde
            ((== q 1))
            ((=/= q 2))))

  (run* (q)
    (fresh (a b c)
          (conde
             ((== a 1) (== b a) (== c a) (=/= c 1))
             ((== a 2)(== b 3)(== c a)))
         (== q `(,a ,b ,c))))

  (run 5 (q)
       (fresh (x y)
              (== x 'pear)
              (=/= y x)
              (== q `(,x ,y))))

  (run 1 (q) (fresh (x y)
                    (== q x)
                    (== `(a b ,x) `(a b c))))

  (funcall (fives-and-sixes) empty-state)

  (take 1 (funcall (fives-and-sixes) empty-state))

  (take 3 (funcall (fives-and-sixes) '((() . 0) . ())))

  (run 5 (q) (fresh (x y)
               (caro `(grape raisin pear) x)
               (caro '((a) (b) (c)) y)
               (== (cons x y) q)))

  (run* (q) (cdro '(acorn pear) q))

  (run* (q) (fresh (v)
                 (cdro '(a c o r n) v)
                 (fresh (w)
                  (cdro v w)
                  (caro  w q))))

  (run 5 (q) (fresh (x y)
                   (cdro '(grape raisin pear) x)
                   (caro '((a) (b) (c)) y)
                   (== (cons x y) q)))

  (run* (q) (cdro '(c o r n) `(,q r n)))

  (run* (q) (fresh (x)
                  (cdro q '(c o r n))
                  (caro q x)
                  (== 'a x)))

  (run* (q) (membero 'olive '(virgin olive oil)))

  (run 1 (q) (membero q '(virgin olive oil)))

  (run 1 (q) (membero q '(olive oil)))

  (run* (q) (caro '(virgin olive oil) 'olive))

  (run* (q) (caro '(virgin olive oil) 'virgin))

  (run 5 (q) (== (cons 'virgin q) '(virgin olive oil)))

  (run* (q) (membero 4 '(1 2 3)))

  (run* (q) (fresh (r)
                  (== `(Result ,r) q)
                  (membero r '(1 2 3))))

  (run 3 (q) (membero 1 q))

  (run* (q) (conso 1 '(2 3) q))

  (run 1 (q) (conso 1 q '(1 2 3)))

  (run* (q) (conso 1 `(2 ,q) '(1 2 3)))

  (run* (q) (fresh (a b)
                   (conso a `(2 ,b) '(1 2 3))
                   (== q (list a b))))

  (run* (x y)
        (appendo x '(3 4 5) '(1 2 3 4 5)))

  ;(runi (x y)
        ;(appendo x y '(1 2 3 4 5)))

  (run 5 (x y) (== x y) (=/= x 5)(=/= y 9)(=/= x 3))

  (run 5 (x y) (conde
                 ((== x y) (=/= x 5)(=/= y 9)(=/= x 3))
                 ((fresh (a b)
                        (== a 3)
                        (== b 9)
                        (== x a)
                        (=/= y b)))))

  (run 5 (x y z) (fresh (a b c)
                        (conde
                          ((== x a)
                           (== b z)
                           (=/= a y)
                           (== z 9)
                           (== a z))
                          ((== x 23)
                           (== c 32)
                           (=/= z y)
                           (=/= y 45)))))

  (run 5 (x y z) (fresh (a b c)
                        (conde
                          ((== x a)
                           (== b z)
                           (=/= a y)
                           (== z 9)
                           (== a z))
                          ((== x 23)
                           (== c 32)
                           (=/= z y)
                           (=/= y 45)
                           (== y 67))))))

;;;;;;;;;;;;;;;;;;;;;;    Parents.......   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun parento (c p)
  (conde
     ((== c 'teddy) (== p 'sarih))
     ((== c 'andrew) (== p 'steve))
     ((== c 'brook)(== p 'steve))
     ((== c 'caroline)(== p 'steve))
     ((== c 'peter) (== p 'steve))
     ((== c 'steve) (== p 'bill))
     ((== c 'roger) (== p 'bill))
     ((== c 'steve) (== p 'katie))
     ((== c 'roger) (== p 'katie))
     ((== c 'will) (== p 'roger))
     ((== c 'andy) (== p 'roger))
     ((== c 'earnest) (== p 'roger))
     ((== c 'jack) (== p 'bill))
     ((== c 'anne) (== p 'john))
     ((== c 'danni) (== p 'john))))

(defun married (h w)
  (conde
    ((== h 'stevie)(== w 'anne))
    ((== h 'nate)(== w 'danni))
    ((== h 'bill)(== w 'katie))
    ((== h 'john)(== w 'kitty))
    ((== h 'andrew)(== w 'saraih))))

(defun grandparent (g s)
  (fresh (p) (parento g p) (parento p s)))

(defun parent1 (c p1)
  (fresh (h)
         (conde
           ((married h p1))
           ((married p1 h)))
         (parento c h)))

(defun parent (c p)
  (fresh (c1 p1 p2)
         (parento c1 p1)
         (parent1 c1 p2)
         (conde
           ((== p `(,p1 . ,p2)))
           ((== p `(,p2 . ,p1))))
         (== c c1)))

(defun cousin (c1 c2)
  (fresh (gp p r)
         (grandparent c1 gp)
         (grandparent c2 gp)
         (parento c1 p)
         (parento c2 r)
         (=/= p r)
         (=/= c1 c2)))

#+nil
(progn
  (run 10 (q) (parent 'danni q))
  (run 10 (q) (grandparent 'danni q))
  (run 10 (q) (grandparent 'peter q))
  (run 10 (q) (grandparent 'will q))
  (run 10 (q) (cousin 'peter q))
  (run 10 (q) (cousin 'andy q)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+nil
(progn
  (run* (q) (fresh (feline rodent reptile
                           bird vertebrate invertebrate mammal animal)
              (conde
               ((== feline 'cat)(== animal feline)(== mammal feline)
                    (=/= feline invertebrate)(=/= feline rodent)
                    (=/= feline reptile)(=/= feline bird))
               ((== rodent 'mouse)(== animal rodent)(== mammal rodent)
                    (=/= rodent invertebrate)(=/= rodent feline)
                    (=/= rodent reptile)(=/= rodent bird))
               ((== feline 'tiger)(== animal feline)(== mammal feline)
                    (=/= feline invertebrate)(=/= feline rodent)
                    (=/= feline reptile)(=/= feline bird))
               ((== feline 'puma)(== animal feline)(== mammal feline)
                    (=/= feline invertebrate)(=/= feline rodent)
                    (=/= feline reptile)(=/= feline bird))
               ((== reptile 'snake)(== animal reptile)(== invertebrate reptile)
                    (=/= vertebrate reptile)(=/= reptile mammal)
                    (=/= reptile rodent)(=/= reptile feline)(=/= reptile bird))
               ((== bird 'colibri)(== animal bird)(== vertebrate bird)
                    (=/= mammal bird)(=/= bird invertebrate)
                    (=/= bird rodent)(=/= bird reptile)(=/= bird feline)))
              (== q animal)
              (== q vertebrate)
              (=/= q mammal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;   THE ZEBRA PUZZLE    ;;;;;;;;;;;;;;;;;;;;;;;;;

;There are  five houses in  a row and  in five different  colors.  In each house
;lives a person  from a different country.  Each person  drinks a certain drink,
;plays a certain sport,  and keeps a  certain pet.  No two people drink the same
;drink, play the same sport, or keep the same pet.

;1 The Brit lives in a red house
;2 The Swede keeps dogs
;3 The Dane drinks tea
;4 The green house is on the left of the white house
;5 The green house owner drinks coffee
;6 The person who plays polo rears birds
;7 The owner of the yellow house plays hockey
;8 The man living in the house right in the center drinks milk
;9 The Norwegian lives in the first house
;10 The man who plays baseball lives next to the man who keeps cats
;11 The man who keeps horses lives next to the one who plays hockey
;12 The man who plays billiards drinks beer
;13 The German plays soccer
;14 The Norwegian lives next to the blue house

;Who Owns the fish?

;;Relations

(defrel (brit-lives-in-red-house solution)
   (fresh (pet beverage sport)
     (let ((house (list 'House 'Brit 'Red pet beverage sport)))
      (membero house solution))))

(defrel (swede-keeps-dogs solution)
  (fresh (color beverage sport)
    (let ((house (list 'House 'Swede color 'Dogs beverage sport)))
      (membero house solution))))

(defrel (dane-drinks-tea solution)
  (fresh (color pet sport)
    (let ((house (list 'House 'Dane color pet 'Tea sport)))
      (membero house solution))))

(defrel (green-house-owner-drinks-coffee solution)
  (fresh (nationality pet sport)
    (let ((house (list 'House nationality 'Green pet 'Coffee sport)))
      (membero house solution))))

(defrel (polo-player-rears-birds solution)
  (fresh (nationality color beverage)
    (let ((house (list 'House nationality color 'Birds beverage 'Polo)))
      (membero house solution))))

(defrel (yellow-house-owner-plays-hockey solution)
  (fresh (nationality pet beverage)
    (let ((house (list 'House nationality 'Yellow pet beverage 'Hockey)))
      (membero house solution))))

(defrel (billiad-player-drinks-beer solution)
  (fresh (nationality color pet)
    (let ((house (list 'House nationality color pet 'Beer 'Billiard)))
      (membero house solution))))

(defrel (german-plays-soccer solution)
  (fresh (color pet beverage)
    (let ((house (list 'House 'German color pet beverage 'Soccer)))
      (membero house solution))))

(defrel (center-house-owner-drinks-milk solution)
  (fresh (h1 h2 h3 h4 h5 nationality color pet sport)
    (let ((street (list 'Street h1 h2 h3 h4 h5))
          (house (list 'House nationality color pet 'Milk sport)))
      (conj (== street solution) (== house h3)))))

(defrel (center-house-owner-drinks-milk/alternate solution)
  (fresh (h1 h2 h3 h4 h5 nationality color pet sport)
    (== `(Street ,h1 ,h2 ,h3 ,h4 ,h5) solution)
    (== `(House ,nationality ,color ,pet 'Milk ,sport) h3)))

(defrel (norvegian-in-first-house solution)
  (fresh (h1 h2 h3 h4 h5 color pet beverage sport)
    (let ((street (list 'Street h1 h2 h3 h4 h5))
          (house (list 'House 'Norvegian color pet beverage sport)))
      (conj
       (== street solution)
       (disj
        (== house h1)
        (== house h5))))))

;;“To-The-Left-Of” relationships
(defrel (to-the-left-of/o house-a house-b solution)
  (fresh (h1 h2 h3 h4 h5)
    (let ((street (list 'Street h1 h2 h3 h4 h5)))
      (== street solution))
    (conde
     ((== h1 house-a) (== h2 house-b))
     ((== h2 house-a) (== h3 house-b))
     ((== h3 house-a) (== h4 house-b))
     ((== h4 house-a) (== h5 house-b)))))

(defrel (green-house-left-of-white-house solution)
  (fresh (nationality1 pet1 beverage1 sport1 nationality2 pet2 beverage2 sport2)
    (let ((green-house (list 'House nationality1 'Green pet1 beverage1 sport1))
          (white-house (list 'House nationality2 'White pet2 beverage2 sport2)))
     (to-the-left-of/o green-house white-house solution))))

;;“Next-To” relationships
(defrel (next-to/o x y l)
  (disj
   (to-the-left-of/o x y l)
   (to-the-left-of/o y x l)))

(defrel (baseball-player-lives-next-to-cat-owner solution)
  (fresh (nationality1 color1 pet1 beverage1 nationality2 color2 beverage2 sport2)
    (let ((baseball-house (list 'House nationality1 color1 pet1 beverage1 'Baseball))
          (cat-house (list 'House nationality2 color2 'Cats beverage2 sport2)))
     (next-to/o baseball-house cat-house solution))))

(defrel (hockey-player-lives-next-to-horse-owner solution)
  (fresh (nationality1 color1 pet1 beverage1 nationality2 color2 beverage2 sport2)
    (let ((hockey-house (list 'House nationality1 color1 pet1 beverage1 'Hockey))
          (horse-house (list 'House nationality2 color2 'Horses beverage2 sport2)))
     (next-to/o hockey-house horse-house solution))))

(defrel (norvegian-lives-next-to-blue-house solution)
  (fresh (color1 pet1 beverage1 sport1 nationality2 pet2 beverage2 sport2)
    (let ((norvegian-house (list 'House 'Norvegian color1 pet1 beverage1 sport1))
          (blue-house (list 'House nationality2 'Blue pet2 beverage2 sport2)))
     (next-to/o norvegian-house blue-house solution))))

;;The beginning....

(defrel (fish-puzzle solution)
  (fresh (h1 h2 h3 h4 h5)
    (let ((street (list 'Street h1 h2 h3 h4 h5)))
      (== street solution)))
  (brit-lives-in-red-house solution))

;;---------------------------------------------
#+nil
(progn
 (run* (solution) (fish-puzzle solution)))
;;---------------------------------------------

;;More.....

(defrel (fish-puzzle solution)
      (fresh (h1 h2 h3 h4 h5)
            (let ((street (list 'Street h1 h2 h3 h4 h5)))
              (== street solution)))
      (brit-lives-in-red-house solution)
      (swede-keeps-dogs solution)
      (dane-drinks-tea solution)
      (green-house-owner-drinks-coffee solution)
      (polo-player-rears-birds solution)
      (yellow-house-owner-plays-hockey solution)
      (billiad-player-drinks-beer solution)
      (german-plays-soccer solution))

;;---------------------------------------------
#+nil
(progn
 (run 3 (solution) (fish-puzzle solution)))
;;---------------------------------------------

;;Almost there...

(defrel (fish-puzzle solution)
  (fresh (h1 h2 h3 h4 h5)
    (let ((street (list 'Street h1 h2 h3 h4 h5)))
      (== street solution)))

  ;; Clues about the houses
  (brit-lives-in-red-house solution)
  (swede-keeps-dogs solution)
  (dane-drinks-tea solution)
  (green-house-owner-drinks-coffee solution)
  (polo-player-rears-birds solution)
  (yellow-house-owner-plays-hockey solution)
  (billiad-player-drinks-beer solution)
  (german-plays-soccer solution)

  ;; Clues about house positions on the street
  (center-house-owner-drinks-milk solution)
  (norvegian-in-first-house solution)

  ;; To-the-left-of clues
  (green-house-left-of-white-house solution)

  ;; Next-to clues
  (baseball-player-lives-next-to-cat-owner solution)
  (hockey-player-lives-next-to-horse-owner solution)
  (norvegian-lives-next-to-blue-house solution))

;;---------------------------------------------
#+nil
(progn
 (run* (solution) (fish-puzzle solution)))
;;---------------------------------------------

;; Neither solution has anything to say about a fish, since the fish does not
;; appear anywhere in the clues. However both solutions contain some placeholder
;; symbols, 0 and 1, indicating that we don't know what pet the German has
;; or what beverage the Norvegian drinks.
;; We can how ask the question “who owns the fish?” using the relation below.
;; Note that this relation takes two arguments both the street and a nationality,
;; which can be used as an output argument to determine the owner.

(defrel (who-owns-the-fish? solution nationality)
  (fresh (color beverage sport)
    (let ((house (list 'House nationality color 'Fish beverage sport)))
      (membero house solution))))

;;---------------------------------------------
#+nil
(progn
  (run* (fish-owner)
    (fresh (solution)
       (fish-puzzle solution)
       (who-owns-the-fish? solution fish-owner)))

  (run* (q)
    (fresh (solution)
      (fish-puzzle solution)
      (who-owns-the-fish? solution 'Norwegian))))
;;---------------------------------------------



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; RELATIONAL INTERPRETER v0 — minimal core (quine/twine playground)
;;;
;;; Small eval-expo: quote / list / vars / lambda / unary application.
;;; Fast and compact. Great for quines & twines (and quick sanity checks).
;;; For synthesis with holes it may return correct-but-spurious solutions:
;;; dead code, overly general guards, etc. (expected in v0).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lookupo (x env te)
  (fresh (y v rest)
         (== `((,y . ,v) . ,rest) env)
         (symbolo y)
        (conde
           ((== y x) (== v te))
           ((=/= y x)(lookupo x rest te)))))

(defun not-in-envo (x env)
  (conde
    ((== '() env))
    ((fresh (y v rest)
            (== `((,y . ,v) . ,rest) env)
            (symbolo y)
            (=/= y x)
            (not-in-envo x rest)))))

(defun proper-listo/v0 (exp env val)
  (conde
    ((== `() exp)
     (== `() val))
    ((fresh (a d v-a v-d)
            (== `(,a . ,d) exp)
            (== `(,v-a . ,v-d) val)
            (eval-expo a env v-a)
            (proper-listo/v0 d env v-d)))))

(defun eval-expo (exp env val)
  (conde
    ((fresh (v)
        (== `(quote ,v) exp)
        (not-in-envo 'quote env)
        (not-in-envo 'closure env)
        (absento 'closure v)
        (== v val)))
    ((fresh (a*)
        (== `(list . ,a*) exp)
        (not-in-envo 'list env)
        (not-in-envo 'closure env)
        (absento 'closure a*)
        (proper-listo/v0 a* env val)))
    ((symbolo exp) (lookupo exp env val))
    ((fresh (rator rand x body env^ a)
        (== `(,rator ,rand) exp)
        (eval-expo  rator env `(closure ,x ,body ,env^))
        (eval-expo rand env a)
        (eval-expo body `((,x . ,a) . ,env^) val)))
    ((fresh (x body)
        (== `(lambda (,x) ,body) exp)
        (symbolo x)
        (not-in-envo  'lambda env)
        (not-in-envo 'closure env)
        (== `(closure ,x ,body ,env) val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; QUINES / TWINES (stress-tests for eval-expo)
;;;
;;; Quine  = program evaluates to itself
;;; Twine  = two different programs evaluate to each other
;;;
;;; NOTE: delaying (=/= p q) is WAY faster (cheaper constraint handling).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+nil
(progn
 (run 1 (q) (eval-expo q '() q))

 (run 1 (x) (fresh (p q) (=/= p q) (eval-expo p '() q) (eval-expo q '() p) (== `(,p ,q) x)))
 (run 1 (x) (fresh (p q) (eval-expo p '() q) (eval-expo q '() p) (=/= p q) (== `(,p ,q) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; RELATIONAL INTERPRETER v1 — extended core (letrec + primitives)
;;;
;;; Single eval-expo with:
;;; - quote / list / vars / lambda / unary application
;;; - letrec for recursion
;;; - primitives: if / null? / cons / car / cdr
;;;
;;; Everything below uses this same interpreter; only the search strategy changes.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proper-listo/v1 (exp env val)
  (conde
    ((== `() exp) (== `() val))
    ((fresh (a d v-a v-d)
       (== `(,a . ,d) exp)
       (== `(,v-a . ,v-d) val)
       (eval-expo/v1 a env v-a)
       (proper-listo/v1 d env v-d)))))

(defun eval-expo/v1 (exp env val)
  (conde

    ;; -----------------------
    ;; quote
    ;; -----------------------
    ((fresh (v)
       (== `(quote ,v) exp)
       (not-in-envo 'quote env)
       (not-in-envo 'closure env)
       (absento 'closure v)
       (== v val)))

    ;; -----------------------
    ;; list
    ;; -----------------------
    ((fresh (a*)
       (== `(list . ,a*) exp)
       (not-in-envo 'list env)
       (not-in-envo 'closure env)
       (absento 'closure a*)
       (proper-listo/v1 a* env val)))

    ;; -----------------------
    ;; if
    ;; (if test conseq alt)
    ;; false is the symbol 'false; everything else is truthy.
    ;; -----------------------
    ((fresh (tst thn els tv)
       (== `(if ,tst ,thn ,els) exp)
       (not-in-envo 'if env)
       (eval-expo/v1 tst env tv)
       (conde
         ((== tv 'false) (eval-expo/v1 els env val))
         ((=/= tv 'false) (eval-expo/v1 thn env val)))))

    ;; -----------------------
    ;; null?
    ;; (null? e) => 'true or 'false
    ;; -----------------------
    ((fresh (e v)
       (== `(null? ,e) exp)
       (not-in-envo 'null? env)
       (eval-expo/v1 e env v)
       (conde
         ((== v '()) (== val 'true))
         ((=/= v '()) (== val 'false)))))

    ;; -----------------------
    ;; cons
    ;; (cons a d)
    ;; -----------------------
    ((fresh (a d va vd)
       (== `(cons ,a ,d) exp)
       (not-in-envo 'cons env)
       (eval-expo/v1 a env va)
       (eval-expo/v1 d env vd)
       (== (cons va vd) val)))

    ;; -----------------------
    ;; car
    ;; (car p)
    ;; -----------------------
    ((fresh (p vp va vd)
       (== `(car ,p) exp)
       (not-in-envo 'car env)
       (eval-expo/v1 p env vp)
       (== (cons va vd) vp)
       (== va val)))

    ;; -----------------------
    ;; cdr
    ;; (cdr p)
    ;; -----------------------
    ((fresh (p vp va vd)
       (== `(cdr ,p) exp)
       (not-in-envo 'cdr env)
       (eval-expo/v1 p env vp)
       (== (cons va vd) vp)
       (== vd val)))

    ;; -----------------------
    ;; letrec (single binding, lambda-only rhs)
    ;; (letrec ((f (lambda (x) fbody))) body)
    ;; Binds f to a closure whose env is (rec-env f env) to avoid cyclic envs.
    ;; -----------------------
    ((fresh (f x fbody body proc env1)
       (== `(letrec ((,f (lambda (,x) ,fbody))) ,body) exp)
       (symbolo f)
       (symbolo x)
       (not-in-envo 'letrec env)
       (not-in-envo 'lambda env)
       (not-in-envo 'closure env)
       (=/= f 'quote) (=/= f 'list) (=/= f 'lambda) (=/= f 'letrec)
       ;; build recursive procedure value
       (== proc `(closure ,x ,fbody (rec-env ,f ,env)))
       ;; extend env for body
       (== env1 `((,f . ,proc) . ,env))
       (eval-expo/v1 body env1 val)))

    ;; -----------------------
    ;; variable
    ;; -----------------------
    ((symbolo exp)
     (lookupo exp env val))

    ;; -----------------------
    ;; application (unary)
    ;; (rator rand)
    ;; Supports closures with env = (rec-env f base-env)
    ;; -----------------------
    ((fresh (rator rand proc x body env^ a call-env)
       (== `(,rator ,rand) exp)
       (eval-expo/v1 rator env proc)
       (eval-expo/v1 rand env a)

       ;; proc is a closure
       (== proc `(closure ,x ,body ,env^))

       ;; compute call-env:
       ;; - normal closure: call-env = env^
       ;; - recursive closure: call-env = ((f . proc) . base-env)
       (conde
         ((== call-env env^)
          (=/= env^ `(rec-env . ,call-env))) ; avoid accidental match (cheap guard)
         ((fresh (f base)
            (== env^ `(rec-env ,f ,base))
            (== call-env `((,f . ,proc) . ,base)))))

       (eval-expo/v1 body `((,x . ,a) . ,call-env) val)))

    ;; -----------------------
    ;; lambda
    ;; -----------------------
    ((fresh (x body)
       (== `(lambda (,x) ,body) exp)
       (symbolo x)
       (not-in-envo 'lambda env)
       (not-in-envo 'closure env)
       (== `(closure ,x ,body ,env) val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; SYNTHESIS MODE A — unguided (holes allowed, spurious answers possible)
;;;
;;; We let eval-expo/v1 solve templates with holes directly.
;;; Works, but may return correct solutions with dead code / overly general guards.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#+nil
(progn
  (run 1 (q x)
    (eval-expo/v1
      `(letrec ((append (lambda (xs)
                          (lambda (ys)
                            (if ,x
                                ys
                                (,q (car xs) ((append (cdr xs)) ys)))))))
         ((append (quote (a b))) (quote (c d))))
      '()
      '(a b c d))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; SYNTHESIS MODE B — guided (bounded + role-aware search)
;;;
;;; Same eval-expo/v1. The difference is how we search:
;;; - bounded generators (Peano depth)
;;; - role-aware grammars (bool / proc / value)
;;; This keeps search finite and usually yields the “standard” minimal solutions.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun nameo (s)
  (conde ((== s 'f0)) ((== s 'f1)) ((== s 'f2)) ((== s 'f3)) ((== s 'f4))
         ((== s 'f5)) ((== s 'f6)) ((== s 'f7)) ((== s 'f8)) ((== s 'f9))))

(defun keyo (s)
  (conde ((== s 'quote)) ((== s 'list)) ((== s 'lambda)) ((== s 'letrec))
         ((== s 'if)) ((== s 'null?)) ((== s 'cons)) ((== s 'car)) ((== s 'cdr))
         ((== s 'true)) ((== s 'false))))

(defun id-o (s)
  ;; identifiers allowed as variables / function names
  (conde ((nameo s)) ((== s 'xs)) ((== s 'ys))))

(defun z? (d) (== d '()))
(defun s? (d d-1) (== d (cons 's d-1)))

(defun peano (n)
  (if (<= n 0) '() (cons 's (peano (1- n)))))

;; if it sees (if HOLE …), HOLE must be bool
(defun bool-deptho (e d)
  (conde
    ((z? d)
     (conde ((== e 'true)) ((== e 'false))
            ((== e `(null? xs))) ((== e `(null? ys)))))  ; tiny base
    ((fresh (d-1)
       (s? d d-1)
       (conde
         ((== e 'true)) ((== e 'false))
         ((fresh (te)
            (== e `(null? ,te))
            (value-deptho te d-1)))
         ((fresh (te a b)
            (== e `(if ,te ,a ,b))
            (bool-deptho te d-1)
            (bool-deptho a d-1)
            (bool-deptho b d-1))))))))

;; if it sees (HOLE arg), HOLE must be proc
(defun proc-deptho (e d)
  (conde
    ((z? d)
     (conde
       ((id-o e))                 ; a named function/var
       ((== e 'append))))         ; if you *bind* append in the program, this helps, optional
    ((fresh (d-1)
       (s? d d-1)
       (conde
         ((id-o e))
         ;; lambda can be a procedure directly
         ((fresh (x body)
            (== e `(lambda (,x) ,body))
            (id-o x)
            (value-deptho body d-1)))
         ;; allow higher-order: (something that evaluates to a proc) applied to one arg
         ((fresh (rator rand)
            (== e `(,rator ,rand))
            (proc-deptho rator d-1)
            (value-deptho rand d-1))))))))

;; if it sees (cons HOLE …), HOLE must be val
(defun value-deptho (e d)
  (conde
    ((z? d)
     (conde
       ((id-o e))
       ((fresh (v) (== e `(quote ,v))))) )
    ((fresh (d-1)
       (s? d d-1)
       (conde
         ((id-o e))
         ((fresh (v) (== e `(quote ,v))))
         ((fresh (a b)
            (== e `(cons ,a ,b))
            (value-deptho a d-1)
            (value-deptho b d-1)))
         ((fresh (p)
            (== e `(car ,p))
            (value-deptho p d-1)))
         ((fresh (p)
            (== e `(cdr ,p))
            (value-deptho p d-1)))
         ((fresh (rator rand)
            (== e `(,rator ,rand))
            (proc-deptho rator d-1)
            (value-deptho rand d-1))))))))

#+nil
(progn
  (run 1 (qx)
    (fresh (x q)
      (bool-deptho x (peano 3))
      (value-deptho q (peano 3))
      (eval-expo/v1
        `(letrec ((append (lambda (xs)
                            (lambda (ys)
                              (if ,x
                                  ys
                                  (cons ,q ((append (cdr xs)) ys)))))))
           ((append (quote (a b))) (quote (c d))))
        '()
        '(a b c d))
      (== `(,x ,q) qx))))
