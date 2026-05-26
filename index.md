---
layout: home
---

# Welcome
This website contains the basic information about the *Introductory Lean Course* for the *Academy of Mathematics and Systems Science* in Beijing, that takes place in May-June 2026.

The teacher is [Filippo A. E. Nuccio](https://perso.univ-st-etienne.fr/nf51454h/) and all material and classes will be in English.

For every lecture, there is a `.md` file (exported also as a `.pdf`), that you find below and that contains all material discussed in class; alongside these files, there is also a `.lean` file shown during class and containing all the exercises, whose solutions are posted the day following the lecture, in general.

The Mathlib `commit` upon which this project is build is [5450b53](https://github.com/leanprover-community/mathlib4/commit/5450b53e5ddc75d46418fabb605edbf36bd0beb6). 

<!-- The documentation for the Mathlib version used in this project is available [here](https://faenuccio-teaching.github.io/Beijing_Jun26/docs/): consider in particular the [tactics page](https://faenuccio-teaching.github.io/Beijing_Jun26/docs/tactics.html).  -->
## Agenda
Classes take place on Saturday, **from 9:00 to 12h00** and then **from 14:00 to 17:00** in the South Building, Room 204.

| Date      | Lecture         | Ancillary Files | Notes
|-----------|---------------|---------------|---------------
| May 30th, morning | Tactics and Types | [Lean File](https://github.com/faenuccio-teaching/Beijing_Jun26/blob/master/BeijingJun26/1_Tactics%26Types.lean) [Markdown](https://github.com/faenuccio-teaching/Beijing_Jun26/blob/master/BeijingJun26/1_Tactics%26Types_lecture.md) [PDF](https://github.com/faenuccio-teaching/Beijing_Jun26/blob/master/BeijingJun26/1_Tactics%26Types_lecture.pdf)|
| May 30th, afternoon | More  on Types | [Lean File](https://github.com/faenuccio-teaching/Beijing_Jun26/blob/master/BeijingJun26/2_MoreTypes.lean)   [Markdown](https://github.com/faenuccio-teaching/Beijing_Jun26/blob/master/BeijingJun26/2_MoreTypes_lecture.md) [PDF](https://github.com/faenuccio-teaching/Beijing_Jun26/blob/master/BeijingJun26/2_MoreTypes_lecture.pdf)|
| June 6th, morning | Algebra 1 | |
| June 6th, afternoon | Algebra 2| |
| June 13th, morning | Sets and Limits | |
| June 13th, afternoon | Advanced topics ||


## References

There aren't many books detailing how `Lean` works, but the beautiful
* [Mathematical Components](https://math-comp.github.io/mcb/), by A. Mahboubi and E. Tassi, 

tailored around the proof assistant [`Rocq`](https://rocq-prover.org/), is an excellent introduction to what the formalisation of mathematics is. The third chapter contains a nice introduction to the "type theory" that we use.

Another survey of what is needed type-theoretically can be found in the first chapter "Type theory" of the
* [Homotopy Type Theory (a.k.a. "HoTT book")](https://homotopytypetheory.org/book/)

A more complete source, extremely well written and a really pleasant read is
* [Lectures on the Curry–Howard Isomorphism](https://www.sciencedirect.com/bookseries/studies-in-logic-and-the-foundations-of-mathematics/vol/149/suppl/C), by M. H. Sørensen et P. Urzyczyn.

 The two `Lean`-oriented references
* [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/), by J. Avigad, L. de Moura, S. Kong et S. Ullrich
* [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/), by J. Avigad et P. Massot

also contain a lot of material relevant to our course.

## Lean and GitHub prerequisites

Before the beginning of the course (on Saturday, May 30th 2026), make sure to:
* have a working internet connection once at the AMSS;
* have a working `git` installation: in case you need help, you can try to have a look at the [nice tutorial](https://www.imo.universite-paris-saclay.fr/~patrick.massot/misc/git.html) maintained by Patrick Massot;
* have an account on [GitHub](https://github.com) to be able to upload your work;
* have a working installation of Lean on your laptop, by following the [offical instructions](https://lean-lang.org/install/). Shall you run into problems, don't panic: we'll have time to debug during the first lecture;
* have downloaded (through `git clone`) the repository of this course, available at [https://github.com/faenuccio-teaching/Beijing_Jun26.git](https://github.com/faenuccio-teaching/Beijing_Jun26.git). After the download, navigate (in the terminal) to the folder and then run the command `lake exe cache get` followed by `lake build`: the first should take 30 seconds to 1 minute to complete, the second should be almost instantaneous, and if this is the case everything is good ;
* have disabled all `Chat AI Features` from VSCode: for this, go to `Settings → Features → Chat` and select `Disable AI Features`. 
