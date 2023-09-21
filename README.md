# sī-Kanren, a  microKanren implementation in Common Lisp, with disequality constraint

*sī-Kanren*     is      based      on      the      2013     Scheme     Workshop
[paper](http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf)   by  Jason
Hemann  and  Dan Friedman.  Other  resources  are  available  on  the miniKanren
[website]( http://minikanren.org).  It's  written  in  "pure"  and simple Common
Lisp,  without external libraries like  pmatch,  guard or things like that,  nor
record types or structs. The **constraint  store** in fact,  as a whole,  has the form:

> cs =  '(((s) . c) .  (d))

where `s` is the  *substitution*,  `c` the *counter* and `d` the *disequality store*.

For more information:
- Excellent survey paper on unification: [Kevin Knight](https://kevincrawfordknight.github.io/papers/unification-knight.pdf).
- Disunification papers: [Hubert Comon , Pierre Lescanne](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.139.4769).
  - [Hubert Comon](https://www.semanticscholar.org/paper/Disunification%3A-A-Survey.-Comon/0d3a871604806c366ce1aa09120eba2964d5f111)
- Combining Unification and Disunification Algorithms: [Klaus U. Schulz](https://www.cis.uni-muenchen.de/otherpublications/cis_berichte/cis-96-099.html).
- And, above all, the [miniKanren uncourse series](https://www.youtube.com/playlist?list=PLO4TbomOdn2cks2n5PvifialL8kQwt0aW), by William Byrd!



### Features

2. `=/=` constraint,  and thus it's  the first microKanren  written in Common  Lisp with this  feature (at
least, as far as I know).
3.  *Reification* of **all** the logic queries variables `x x0...` in `(run _ (x x0...)...)`.  It looks
like a trick of magic too beautiful to not include it. :magic_wand:
4. *Interactive* request of a solution/s, with `runi`.
5. Pretty *formatting* of the answer/s.


### Installation
*sī-Kanren* is a library in [Quicklisp](https://www.quicklisp.org/beta/). To **load** it, use:
#+BEGIN_SRC lisp
(ql:quickload "si-kanren")
#+END_SRC

### Usage[^0]
Many examples can be found in the *playground* file.


### Credits
- Inspiration for a simple implementation in Common Lisp, from [cl-microkanren](https://github.com/blasut/cl-microkanren).

- Inspiration for the implementation of the disequality store, from [microKanren-sagittarius](https://github.com/orchid-hybrid/microKanren-sagittarius).

- I took the *Zebra Puzzle* example [here](https://alex-hhh.github.io/2021/08/fish-puzzle.html)[^1].

- The version of the *nlet-tail* macro (among others things), from [Let Over Lambda](https://letoverlambda.com/), by Doug Hoyte (@hoytech).

- And, of course, last but not least, many thank's to @webyrd for his sensational [work](https://github.com/webyrd)!

As for the name, *sī*    is the Chinese unit of measurement for **10** *micro*meters:
since compared to microKanren *sī-Kanren* also contains the disequality store, it seemed
to me a fair way to give credit to this system. :grin: And since I think it can
be pronounced like a *c* (more or less...), as in **C**ommon Lisp, the **c**ircle **c**loses[^2].

[^0]: Tested on SBCL v. 2.3.0
[^1]: @alex-hhh Hope it's ok for you! Here's the [CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) license link.
[^2]: Cit.: The Stand, Stephen King
