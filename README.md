# sī-Kanren, a  microKanren implementation in Common Lisp, with disequality constraint

*sī-Kanren*     is      based      on      the      2013     Scheme     Workshop
[paper](http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf)   by  Jason
Hemann  and  Dan Friedman.  Other  resources  are  available  at  the miniKanren
[website]( http://minikanren.org).  It's  written  in  "pure"  and simple Common
Lisp,  without external libraries like  pmatch,  guard or things like that,  nor
record types or structs. The **constraint  store** in fact,  as a whole,  has the form:

> cs =  '(((s) . c) .  (d))

where `s` is the  *substitution*,  `c` the *counter* and `d` the *disequality store*.

For more information:
- Excellent survey paper on unification: [Kevin Knight](http://www.isi.edu/natural-language/people/unification-knight.pdf).
- Disunification papers: [Hubert Comon , Pierre Lescanne](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.139.4769).
  - [Hubert Comon](http://citeseer.uark.edu:8080/citeseerx/viewdoc/summary?doi=10.1.1.48.8234)
- Combining Unification and Disunification Algorithms: [Klaus U. Schulz](https://www.cis.uni-muenchen.de/otherpublications/cis_berichte/cis-96-099.html).
- And, above all, the [miniKanren uncourse series](https://www.youtube.com/playlist?list=PLO4TbomOdn2cks2n5PvifialL8kQwt0aW), by William Byrd!



### Features
*sī-Kanren* includes:
1. core miniKanren (`fresh`,  `conde`,  `==`).
2. `=/=` constraint,  and thus it's  the first microKanren  written in Common  Lisp with this  feature (at
least, as far as I know).
3.  Reification of **all** the logic queries variables `x x0...` in `(run _ (x x0...)...)`.  It looks
like a trick of magic too beautiful to not include it. :magic_wand:
4. *Interactive* request of a solution/s, with `runi`.
5. Pretty *formatting* of the answer/s.

### Usage[^0]
Many examples can be found in the *playground* file.


### Credits
- Inspiration for a simple implementation in Common Lisp, from [cl-microkanren](https://github.com/blasut/cl-microkanren)[^1].

- Inspiration for the implementation of the disequality store, from [microKanren-sagittarius](https://github.com/orchid-hybrid/microKanren-sagittarius).

- I took the *Zebra Puzzle* example [here](https://alex-hhh.github.io/2021/08/fish-puzzle.html)[^2].

- The version of the *nlet-tail* macro (among others things), from [Let Over Lambda](https://letoverlambda.com/), by Doug Hoyte (@hoytech).

- And, of course, last but not least, many thank's to @webyrd for his sensational [work](https://github.com/webyrd)!

As for the name, *sī*    is the Chinese unit of measurement for **10** micrometers:
since compared to microKanren *sī-Kanren* also contains the disequality store, it seemed
to me a fair way to give credit to this system. :grin: And since I think it can
be pronounced like a *c* (more or less...), as in **C**ommon Lisp, the **c**ircle **c**loses[^3].

[^0]: Tested on SBCL v. 2.3.0
[^1]: @blasut Thank's for your work! By the way, I think there's really no need
to carry around this `'false` thing, just stick to a plain and lispy list of...
nothing. But, it was useful to me in the first place to discover a subtle bug in the disequality store (because you can't *normalize* 'false; I know, not your problem),
without which I could have been totally not aware! So, for me, the
moral of this story is... testing!
[^2]: @alex-hhh Hope it's ok for you! Here's the [CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) license link.
[^3]: Cit.: The Stand, Stephen King
