---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

layout: home
title: Proving TCS and Math Theorems in Lean
---

![Course Logo](assets/logo.jpg){: style="float: right; width: 300px; margin-left: 20px;"}

**Instructor:** [Venkatesan Guruswami](https://people.eecs.berkeley.edu/~venkatg)  
**Lecture time:** Friday 13:00–15:00  
**Location:** SODA 320  
**Guest Lecturer:** [Pritish Kamath](https://pritishkamath.github.io)  
**TA:** [Shilun (Allan) Li](https://shilun-allan-li.github.io/)  
**Office hours:** 
<br>Venkat: By Appointment
<br>Shilun: Friday 15:00-16:00 (SODA 411)

* TOC
{:toc}

## Course Description

This course introduces the use of the [Lean 4](https://lean-lang.org/) proof
assistant to formalize concepts and results from theoretical computer science
and mathematics. The first part of the course covers the fundamentals of Lean 4,
including its logical foundations, core syntax, and proof tactics, through
guided exercises and examples.

Students will then form small groups and undertake a semester-long formalization
project on a selected topic, such as automata theory, computability, complexity
theory, or combinatorics. The course emphasizes hands-on engagement with Lean
and aims to provide students with practical experience in mechanized reasoning
and formal proof development.

## Grading
Class Participation 10%<br>
Homework 30%<br>
Final Project 60% 

## Lectures
{% include lecture-list.html %}

## Problem Sets
<!-- - [Problem Set 1 (Lean file)](/LeanSource/PSets/PSet1.lean) -->
### Problem Set Mathlib Project Folder [[Download]](/psets/pset.zip)
- **PS1 (Due 02/05)**:
  [[View On Github]](https://github.com/ucb-lean-course-sp26/ucb-lean-course-sp26.github.io/tree/main/psets/pset1.lean)
  [[Download]](/psets/pset1.lean)
  [[Solutions]](https://github.com/ucb-lean-course-sp26/ucb-lean-course-sp26.github.io/tree/main/psets/pset1sol.lean)
- **PS2 (Due 02/19)**:
  [[View On Github]](https://github.com/ucb-lean-course-sp26/ucb-lean-course-sp26.github.io/tree/main/psets/pset2.lean)
  [[Download]](/psets/pset2.lean)
  [[Solutions]](https://github.com/ucb-lean-course-sp26/ucb-lean-course-sp26.github.io/tree/main/psets/pset2sol.lean)
- **PS3 (Due 03/05)**:
  [[View On Github]](https://github.com/ucb-lean-course-sp26/ucb-lean-course-sp26.github.io/tree/main/psets/pset3.lean)
  [[Download]](/psets/pset3.lean)

## AI policy
You are welcome to use any AI tool to ask **general questions** about Lean4 syntax, tactics, and mathlib theorem usage.

However, you **may not** copy homework problems into AI tools or ask AI to produce homework solutions, and you may not submit AI-generated homework answers as your own work.

For the **final project**, you are welcome to use any AI tool without restriction.


## Additional References

Installing / running Lean4:
- (Recommended) Via [VSCode Extension](https://lean-lang.org/install/).
- [Online Lean4 IDE](https://live.lean-lang.org/) with latest mathlib4.

Books:
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/):
Book by [Jeremy Avigad](https://www.andrew.cmu.edu/user/avigad/),
[Patrick Massot](https://www.imo.universite-paris-saclay.fr/~patrick.massot/en/).
- [The Mechanics of Proof](https://hrmacbeth.github.io/math2001/):
Book by [Heather Macbeth](https://www.ma.imperial.ac.uk/~hmacbeth/).
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/):
Book by [Jeremy Avigad](https://www.andrew.cmu.edu/user/avigad/), 
[Leonardo de Moura](https://leodemoura.github.io/), 
[Soonho Kong](https://soonhokong.github.io/), 
and [Sebastian Ullrich](https://sebasti.a.nullri.ch/).

Other similar courses:
- [Proving theorems in Lean](https://yuvalfilmus.cs.technion.ac.il/courses/?crid=1777):
Course by [Yuval Filmus](https://yuvalfilmus.cs.technion.ac.il/).
- [Proofs and Programs](https://math.iisc.ac.in/~gadgil/proofs-and-programs-2025/index.html):
Course on introduction to interactive theorem proving using Lean by [Siddhartha Gadgil](https://math.iisc.ac.in/~gadgil/).
- [EPFL Lean mini course](https://github.com/b-mehta/epfl-comb):
Adapted from *Mathematics in Lean* and the
[Lean for the Curious Mathematician 2023 workshop](https://lftcm2023.github.io/).
- [Logical Verification 2025 (Lean Forward)](https://github.com/lean-forward/logical_verification_2025):
Course materials and repository for the Lean Forward Logical Verification 2025 program.

Miscellaneous:
- [Loogle!](https://loogle.lean-lang.org/): Search engine for Lean 4.
- [mathlib4](https://leanprover-community.github.io/mathlib4_docs/Mathlib)
documentation.
- Lean community [Zulip channel](https://leanprover.zulipchat.com/) for
questions and discussions.
- [ECClib Project](https://shilun-allan-li.github.io/tcslib/) by Venkatesan Guruswami, Shilun Li, Henry Li, Frederick Dehmel, Annie Yao et al.
