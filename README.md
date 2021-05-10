# program-analysis-using-constraints-jeremyberchtold
program-analysis-using-constraints-jeremyberchtold created by GitHub Classroom

# Overview of work I did:
## Z3
Spent about 3 to 3.5 hours learning Z3 and applying the constraints from the first example we went over in class (true => I[-50/x], etc.) but couldn't get Z3 to solve it without Z3 looping indefinitely or saying unsat.

I started with a few simple examples of Z3 from tutorials I found online. I started with solving for simple predicate functions that took an integer and output a boolean. I attempted to solve for a simple formula for prime numbers under 10,000, using a long list of Z3 asserts generated from a python script. The resulting solved function was just a giant set of ifs where it had just memorized all the primes I gave as input. Not what I was looking for, but it gave me some insight into how SMT solvers will give anything as a solution that is technically correct, even if human coders would dismiss it as a solution because it isn't practical.

From there, I started to try to encode the loop invariants into Z3. I started encoding the constraints in an incorrect way since I didn't fully understand the paper yet. I tried to solve for two functions, one for x and one for y. Then I tried to solve for the various constraints listed in the paper, (loopX(x,y) should produce x+y, loopY(x,y) should produce y+1, etc.). This definitely did not work, but it was helpful to try out since I was still wrapping my head around the paper and SMT solvers.

After that I looked at the paper some more and reviewed my notes in more detail. I tried again at the example we covered in class with a1-a6. I wrote `I` as a function that takes x and y and produces a boolean, which was my understanding from the paper. However, I was not solving for `I`, I was using the general constraint implementation we covered in class that uses a1-a6, so we don't have to solve for an arbitrary expression, we can solve for 6 (or more if needed) arbitrary integer constants, which is an easier problem. I then encoded each of the implications listed in the example, true => I\[-50/x\], I or x < 0 => I\[(y+1)/y, (x+y)/x\], and I or x >= 0 => y > 0. I used the implication formula where an implication A => B is equivalent to (not A or B). The solver was able to solve the first two constraints and produce a solution (which don't reference our assert(y>0), so aren't a complete solution). However, when I got to the 3rd constraint, it looped indefinitely. I tried different solvers and nothing worked. I think I must have misunderstood part of the paper or Z3. I did want to get something working though, so I worked on constraint generation instead.

## Racket Constraint Generation
Spent a little under 2 hours working on constraint generation in Racket given an Sexpr that represents some basic code control flow. I produced what I believe is constraint generation, in that I generated the list of implications from input code. However, my terminology may be slightly off and the constraints may be the a1-a6 solved expression for `I` which I attempted earlier, but this Racket code does not solve for.

The code takes Sexpr input that resembles the code from the paper and outputs a list of implications.

```
((set x 10) (while (>= x 0) (set x (- x 1)) (assert (< x 0)))))
```
outputs
```
(list (implication 'true '(I ((x 10))))
		  (implication '(>= x 0) '(I ((x (- x 1)))))
		  (implication '(< x 0) '(< x 0))))
```

The basic idea of the code is that is has a main function called `find-constraints`. This function handles each statement type differently (`set`, `assert`, `while`, etc.). For example, `set` will always produce an implication of the form true => (var value) where var and value are the variable name and constant value assigned. This represents the same thing as `x = -50` at the beginning of the loop in the example from the paper. The `find-constraints` function does the bulk of the logic of generating constraints, however I do have a couple helper functions that perform simpler common operations like inverting the condition of a boolean expression (converts (> x 0) to (<= x 0), etc.) and adding conditions to an implication. The overall idea of the algorithm is to solve for the atomic statements first (`set` and `assert`) and which both have true for the left side of the implication. Then the more complex rules like `while` and `ite` (if-then-else) add their conditions to the left side of the implication. Multiple statements listed sequentially will simply concatenate all their resulting implications.
