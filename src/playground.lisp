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

(run 10 (q) (parent 'danni q))
(run 10 (q) (grandparent 'danni q))
(run 10 (q) (grandparent 'peter q))
(run 10 (q) (grandparent 'will q))
(run 10 (q) (cousin 'peter q))
(run 10 (q) (cousin 'andy q))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
            (=/= q mammal)))

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
(run* (solution) (fish-puzzle solution))
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
(run 3 (solution) (fish-puzzle solution))
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
(run* (solution) (fish-puzzle solution))
;;---------------------------------------------

;; Neither solution has anything to say about a fish, since the fish does not
;; appear anywhere in the clues. However both solutions contain some placeholder
;; symbols, _.0 and _.1, indicating that we don’t know what pet the German has
;; or what beverage the Norvegian drinks.
;; We can how ask the question “who owns the fish?” using the relation below.
;; Note that this relation takes two arguments both the street and a nationality,
;; which can be used as an output argument to determine the owner.

(defrel (who-owns-the-fish? solution nationality)
  (fresh (color beverage sport)
    (let ((house (list 'House nationality color 'Fish beverage sport)))
      (membero house solution))))

;;---------------------------------------------
(run* (fish-owner)
  (fresh (solution)
     (fish-puzzle solution)
     (who-owns-the-fish? solution fish-owner)))

(run* (q)
  (fresh (solution)
    (fish-puzzle solution)
    (who-owns-the-fish? solution 'Norwegian)))
;;---------------------------------------------
