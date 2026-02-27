---
layout: lecture
title: "Lecture 1: Syntax, Formalization, Goals & Tactics"
date: 2026-01-23
slides_url: https://docs.google.com/presentation/d/1zfPAqFHUYklI_ZA3TF1IO7hFyTTQfFoJBE7cW4x0oVM/edit?usp=sharing
demo_url: https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fucb-lean-course-sp26%2Fucb-lean-course-sp26.github.io%2Frefs%2Fheads%2Fmain%2FLeanSource%2FDemos%2FLec1.lean
demo_sol_url: https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fucb-lean-course-sp26%2Fucb-lean-course-sp26.github.io%2Frefs%2Fheads%2Fmain%2FLeanSource%2FDemos%2FLec1sol.lean
---

* TOC
{:toc}

## Motivation

* **The "Paper Review" Crisis:** As proofs become increasingly intricate, with
subtle corner cases, complex inductive steps, probability bounds that are easy
to hand-wave, it is important to have a foundation that is formally verified
to ensure that our foundational results are built on bedrock rather than sand.
* **Lean is Ready for "Real" Math:** Interactive theorem proving is no longer
a wishful dream. Lean has achieved stunning milestones. See for example,
[Liquid Tensor Experiment](https://github.com/leanprover-community/lean-liquid),
[Polynomial Freiman-Ruzsa (PFR) theorem](https://teorth.github.io/pfr/).
* **Improving AI through formal verification:** Pairing AI with a formal
verification system can unlock new capabilities. Some relevant references:
[AlphaProof](https://www.nature.com/articles/s41586-025-09833-y),
[DeepSeek-Prover](https://arxiv.org/abs/2504.21801),
[LeanCopilot](https://github.com/lean-dojo/LeanCopilot),
[Harmonic Aristotle](https://aristotle.harmonic.fun/). See also
[LeanDojo](https://leandojo.org/) and
[Open AI Lean Gym](https://github.com/openai/lean-gym).

### Brief History of Formal Verification in Mathematics

Late 19th-century mathematics faced paradoxes (e.g., Russell's Paradox) that
threatened the validity of all proofs. Russell & Whitehead (in Principia
Mathematica) attempted to derive all mathematics from logic. They created
_Type Theory_ to avoid self-contradiction, which as we will see in this course,
is the "DNA" of Lean's type system. Hilbert sought a "decision procedure" for
mathematics --- a way to prove any statement via a finite set of rules. This
formalized the idea that math can be treated as a structured, symbolic language.

Lean is the modern realization of these dreams. It uses Type Theory (Russell)
to organize data and Formal Logic (Hilbert) to ensure that every step of a proof
is computationally verified.

Several other proof assistants exist that predate Lean. We highlight some of
them below (not exhaustive!):
* [Logic for Computable Functions (LCF)](https://en.wikipedia.org/wiki/Logic_for_Computable_Functions)
is an interactive automated theorem prover developed by
[Robin Milner](https://en.wikipedia.org/wiki/Robin_Milner) and collaborators in
early 1970s, based on the theoretical foundation of
[logic of computable functions](https://en.wikipedia.org/wiki/Logic_of_Computable_Functions)
previously proposed by [Dana Scott](https://en.wikipedia.org/wiki/Dana_Scott).
* [Rocq](https://rocq-prover.org/) (formerly known as "Coq") is an interactive
theorem prover, using Dependent Type Theory, for mechanised reasoning in
mathematics, computer science and more. Many notable theorems have been proved
in Rocq, such as, the
[Graph Four-Color Theorem](https://github.com/rocq-community/fourcolor),
[Busy Beaver Function BB(5)](https://arxiv.org/abs/2509.12337). See
[100 Theorems in Rocq](https://madiot.fr/coq100/) for more examples.
* [Isabelle](https://isabelle.in.tum.de/) automated theorem prover is a
higher-order logic (HOL) theorem prover. A large number of results in
mathematics have been formalized in Isabelle, such as, the
[Prime Number Theorem](https://arxiv.org/abs/cs/0509025),
[Kepler's conjecture](https://arxiv.org/abs/1501.02155),
[Brouwer's Fixed Point Theorem](https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Brouwer_Fixpoint.html),
etc. See
[Top 100 Theorems in Isabelle](https://cgi.cse.unsw.edu.au/~kleing/top100/) for
more examples.

Lean has emerged as a modern favorite for proving theorems owing to the
following reasons:
* The development of [Mathlib](https://github.com/leanprover-community/mathlib4),
which is one massive centralized library developed as a community effort.
* Lean is a general purpose high-performance functional programming language,
that also happens to be a theorem prover.
* Lean's [Metaprogramming](https://leanprover-community.github.io/lean4-metaprogramming-book/)
framework makes it readily extensible.
* Lean has better tooling, such as its integration with VS Code, providing
a smooth "real-time" experience.

### Why this course?

While pure mathematics has huge coverage in Lean's `Mathlib`, theoretical
computer science remains a largely unexplored frontier. We hope that through
course projects, the students of this course would advance the state of Lean
for TCS.

We highlight some such efforts:
* [CS Lib](https://www.cslib.io/) ([GitHub](https://github.com/leanprover/cslib))
* [ECC Lib](https://shilun-allan-li.github.io/tcslib/)

## Installing / Running Lean

There are two main ways to use Lean:

#### VS Code (Recommended)

The best experience is obtained by installing Lean locally, by following a three
step process listed [here](https://lean-lang.org/install/).
1. Install [VS Code](https://code.visualstudio.com/).
2. Install the official **Lean 4** extension in VS Code.
3. Complete the extension setup by following the steps in VSCode.

#### Lean 4 Web

You can also try Lean in your browser (without any installation) using
[Lean 4 Web](https://live.lean-lang.org/).


## 1\. Terms and Types

In Lean, everything is a **term**, and every term has a **type**. This is the core judgment of the system, written as `t : T` (read: "term $t$ has type $T$").

* **Data Examples:**
    * `5` is a term. Its type is `Nat`.
    * `"Hello"` is a term. Its type is `String`.
* **The "Type" of Types:**
    * `Nat` is a term. Its type is `Type`.
    * `Type` is a term. Its type is `Type 1`. (It's turtles all the way up\!)
* **Logical Examples:**
    * `4 = 4` is a term (a proposition). Its type is `Prop`.
    * As we will see later, propositions are in fact types. The term
      `Eq.refl 4` is of type `4 = 4`. (We will get into what this means
      later.)

### Transient Commands

These are commands used to query the system. They do not affect the environment permanently.

`#check <term>`: Asks Lean "What is the type of this?" (The most useful command).
```lean
#check 5    -- 5 : Nat
```
`#eval <term>`: Asks Lean's Virtual Machine to compute the value *Note:* You cannot `#eval` a theorem, only data.
```lean
#eval 2 + 2    -- 4
```

`#print <name>`: Shows internal definition of object.

## 2\. Definitions and Theorems

Lean distinguishes between *data* (programs we run) and *propositions*
(statements we prove).

**`def`**: Used for data, functions, and definitions where the *computational
content* matters.
```lean
def functionName (arg1 : Type1) (arg2 : Type2) : ReturnType :=
  body
```

For example,
```lean
def f (x y : Nat) : Nat := x * y
```

**`theorem`** (or **`lemma`**): Used for mathematical statements. Semantically,
`theorem` and `lemma` are identical. We use them to signal intent. We usually
don't care *how* a theorem is proved (proof irrelevance), only that it is true.
```lean
theorem theoremName (arg1 : Type1) (arg2 : Type2) : theoremStatement :=
  body
```

For example,
```lean
theorem inEq (a b c : Nat) (h : b < c) : a + b < a + c := by
  exact Nat.add_lt_add_left h a
```

Here, `a`, `b`, `c` have type `Nat` and `h` has type `b < c` (recall,
propositions are types!) and the required proof is of type `a + b < a + c`.
In particular, the type of `h` depends on the values of the arguments received
before. This is what is meant by Dependent Type theory.

The Curry-Howard correspondence captures this direct relationship between
"proofs and programs" and "propositions and types".

**`example`**: An anonymous definition. Great for scratchpad work or testing a proof without adding it to the global namespace.
```lean
example (arg1 : Type1) (arg2 : Type2) : exampleStatement :=
  body
```

**`abbrev`**: Like `def`, but tells the kernel to unfold (expand) the definition eagerly. Useful for type aliases.

```lean
abbrev NatPairList := List (Nat × Nat)
```

## 3\. Binders: Explicit, Implicit, and Instance

This is the machinery that allows Lean to be concise.

### A. Explicit Binders `(x : α)`

This is the standard function argument. You must provide it every time.

**Example: The Identity Function**

```lean
-- We define a function 'f' that takes a type 'α' (which is a Sort)
-- and a value 'a' of that type, and returns 'a'.
def f (α : Type) (a : α) : α := a

#eval f Nat 5       -- Output: 5
#eval f String "Hi" -- Output: "Hi"
```

*Problem:* It is tedious to type `Nat` or `String` every time. Lean should be able to guess `α` based on the fact that `5` is a `Nat`.

### B. Implicit Binders `{x : α}`

Curly braces tell Lean: "Figure this argument out yourself from context."

**Example: The Implicit Identity**

```lean
def g {α : Type} (a : α) : α := a

#check g 5        -- Lean infers α = Nat
#eval g "Hello"   -- Lean infers α = String

-- If Lean can't guess it, we can force it using `@`:
#check @g Nat 5
```

### C. Instance Binders `[x : α]`

Square brackets tell Lean: "Look in your database of known classes to find this." This is used for Type Classes (like definitions of groups, rings, or simpler things like 'Printable' or 'Addable').

**Motivation:**
If we try to write a generic addition function:

```lean
def genericAdd {α : Type} (a b : α) : α := a + b -- ERROR!
```

Lean complains: "I don't know if type `α` supports addition\!"

**Solution:**

```lean
def genericAdd {α : Type} [Add α] (a b : α) : α := a + b
```

When we call `genericAdd 5 3`, Lean looks for an "Instance" that explains how
`Nat` supports `Add`.

## 4\. Structure and Inductive Types (Data Structures)

We can define our own types from scratch using `structure` and `inductive`.

### Structure ("Product" or "And") types

A `structure` defines a type that is the product of multiple types. Below, we
provide an example of a `structure` and its corresponding methods.

```lean
structure Rectangle where
  width : Float
  height : Float

namespace Rectangle

  /-- Area of the rectangle. -/
  def area (r: Rectangle) : Float := r.width * r.height

  /-- Perimeter of the rectangle. -/
  def perimeter (r: Rectangle) : Float := 2 * (r.width + r.height)

end Rectangle

def r : Rectangle := { width := 2.0, height := 3.0 }

#eval r.area        -- 6.0000
#eval r.perimeter   -- 10.0000
```

### Inductive ("Sum" or "Or") types

#### Enumerative Types

The simplest use case of an `inductive` type is to define an enumerative type.

```lean
inductive Day where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
```

This defines a type `Day` which takes one of 7 possible values.

#### Recursive types

However, a more interesting case is that of `inductive` types that are defined
recursively. In particular, the type `Nat` of natural numbers is defined as
follows in Lean

```lean
inductive Nat where
  | zero               -- "zero" is a Nat
  | succ : Nat → Nat   -- "succ k" is a Nat for any k : Nat
```

This defines terms of `Nat.zero` (equivalent to `0`),
`Nat.zero.succ` (equivalent to `1`),
`Nat.zero.succ.succ` (equivalent to `2`), etc. For example, you can check
this using

```lean
#eval Nat.zero.succ = 1      -- true
```

Next, we provide an example for how to define $\\{0, 1\\}^*$ as an `inductive`
type.

```lean
inductive BinStr where
  | eps
  | zero: BinStr → BinStr
  | one: BinStr -> BinStr

#check BinStr.eps              -- corresponds to empty string
#check BinStr.eps.zero         -- corresponds to “0”
#check BinStr.eps.zero.one     -- corresponds to “01”
```

We can operate on `inductive` types using `match ... with`, as shown in the
following example, for computing $S(n) := \sum_{k=0}^n k$.
```lean
def sumFirstN (n : Nat) : Nat :=
    match n with
    | Nat.zero => 0
    | Nat.succ k => sumFirstN k + k + 1
```

## 5\. Some Examples in Theorem Formalization

Let's look at how we translate a math problem into Lean.

### Simple Arithmetic

```lean
theorem simple_math : 2 + 5 = 7 := by
  rfl -- "Reflexivity" (by definition, they are equal)
```

### Fermat's Last Theorem
For all $n > 2$, there do not exist $a, b, c > 0$ such that $a^n + b^n = c^n$.

```lean
theorem fermatsLastTheorem
  (n a b c : Nat) (hn : n > 2) (ha : a > 0) (hb : b > 0) (hc : c > 0)
:
  a^n + b^n ≠ c^n
:= by
  sorry
```

`sorry` is a placeholder to tell Lean that we will be filling in the proof
later. The proof is not complete if it has a `sorry`, but Lean stops complaining
when it sees a `sorry`.

### Sum of squares of first $n$ natural numbers
To formalize
$$\sum_{i=0}^{n-1} i = \frac{n(n-1)}{2},$$
we need:

1.  A definition of `sum` (recursive function).
2.  Implicit binders (so we don't have to specify we are working in `Nat`).
3.  The theorem statement.

<!-- end list -->

```lean
/--
  sumFirstN(n) = sum_{k=0}^n k
-/
def sumFirstN (n : Nat) :=
  match n with
  | 0 => 0
  | k + 1 => sumFirstN k + k + 1

/--
  Identity: sum_{k=0}^{n} k = n * (n + 1) / 2
-/
theorem sumOfFirstNFormula (n : Nat) : 2 * sumFirstN n = n * (n + 1) := by
  sorry
```

Or let's consider something more general:
$\sum_{k=0}^n k^2 = \frac{n(n+1)(2n+1)}6$

```lean
/--
 sumSeq(f, n) = sum_{k=0}^n f(k)
-/
def sumSeq {α : Type} [Add α] (f : Nat → α) (n : Nat) :=
  match n with
  | 0 => f 0
  | d + 1 => sumSeq f d + f (d + 1)

def square (x : Nat) := x * x

-- or more generally:
def square {α : Type} [Mul α] (x : α) := x * x

theorem sum_of_squares (n : Nat) :
  6 * sumSeq square n = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ d hd => sorry
```

### Collatz conjecture

The Collatz conjecture states that for all $n > 0$, repeated application of the following function makes the value $1$:

$$
f(x) := \begin{cases}
x/2 & \text{if } x \text{ is even} \\
3x + 1 & \text{if } x \text{ is odd}
\end{cases}
$$

```lean
/--
  The Collatz Map: if n is even, n/2, else 3n + 1.
-/
def collatzMap (n : Nat) : Nat :=
  if n % 2 == 0 then
    n / 2
  else
    3 * n + 1

/--
  Returns f applied d times on n.
  Note: In Lean's standard library, this is `Nat.iterate`.
-/
def applyN (f : Nat → Nat) (d n : Nat) : Nat :=
  match d with
  | 0 => n  -- Base case: Applying f zero times returns n (Identity)
  | k + 1 => applyN f k (f n)  -- Recursive step

/--
  The Collatz conjecture: For all n > 0, there exists d such that
  f^d(n) = 1, for the Collatz map f.
-/
theorem collatzConjecture (n : Nat) (h : n > 0) :
  ∃ d : Nat, applyN collatzMap d n = 1 := by
  sorry
```

## 6\. Introduction to Simple Tactics

### rfl (Reflexivity)

The `rfl` tactic is used to prove goals that are true **by definition**
(*definitionally equal*).

**Usage**
- Use it when the Left Hand Side (LHS) evaluates to exactly the same term as the Right Hand Side (RHS).
- Automatically handles simple computations.

```lean
example : 2 + 2 = 4 := by
  rfl

example (a : Nat) : a = a := by
  rfl
````

### intro (Introducing Hypotheses)

The `intro` tactic moves premises from the goal into the local context.

**Usage**

* Essential for proving implications (`→`) and universal quantifiers (`∀`).
* You can name introduced variables immediately.

```lean
example (p q : Prop) : p → q → p := by
  intro h_p h_q
  exact h_p
```

### exact (Exact Match)

The `exact` tactic closes the goal by providing a term whose type **exactly matches** the goal.

**Usage**

* If you already have a hypothesis of the required type, `exact` finishes the proof.
* The match must be definitional.

```lean
example (p : Prop) (h : p) : p := by
  exact h
```

### apply (Backward Reasoning)

The `apply` tactic works backwards by matching the goal with the conclusion of a lemma or function.

**Usage**

* If the goal is `Q` and you have `h : P → Q`, `apply h` changes the goal to `P`.

```lean
example (p q : Prop)
        (h_imp : p → q) (h_p : p) : q := by
  apply h_imp
  exact h_p
```

### rw (Rewrite)

The `rw` tactic rewrites terms using an equality hypothesis.

**Usage**

* If `h : a = b`, then `rw [h]` replaces `a` with `b`.
* Use `rw [← h]` to rewrite right-to-left.

```lean
example (a b c : Nat)
        (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]
  exact h2
```

### simp (Simplifier)

The `simp` tactic automatically simplifies goals using a database of rewrite rules.

**Usage**

* Very effective for arithmetic identities, boolean logic, and standard definitions.
* Unlike `rw`, it performs many rewrites automatically.

```lean
example (x : Nat) : x + 0 = x := by
  simp

example (p : Prop) : p ∧ True ↔ p := by
  simp
```

While `simp` automatically figures out which rule to use to simplify, it is
good practice to be aware of which rule is precisely being used.
This can be done by writing `simp?`, which points out the rule being used in
the InfoView. In the above example, it is `simp [Nat.add_zero]` and
`simp [and_true]` respectively.

### cases (Case Analysis)

The `cases` tactic performs case analysis on inductive types.

**Common uses**

* `∨` (Or): splits into left and right cases
* `∧` (And): extracts components
* `Nat`: splits into `zero` and `succ n`

```lean
example (n : Nat) : n = 0 ∨ n ≠ 0 := by
  cases n with
  | zero =>
      left --we will get to this in Lecture 3
      rfl
  | succ k =>
      right --we will get to this in Lecture 3
      intro h
      cases h
```

### have (Intermediate Goals)

The `have` tactic introduces and proves a local lemma inside a proof.

**Usage**

* Useful for structuring longer proofs.
* Adds the proven statement to the context.

```lean
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  have hq : q := by 
    apply hpq
    exact hp
  exact hq
```

### induction (Inductive Proofs)

The `induction` tactic is like `cases`, but also provides an **induction hypothesis**.

**Usage**

* Essential for `Nat`, `List`, `Tree`, and other inductive types.
* Produces a base case and an inductive step.

```lean
example (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.add_succ, ih]
```

### constructor (Constructing Data)

The `constructor` tactic applies the canonical constructor of the goal’s inductive type.

**Usage**

* `∧` (And): splits into two subgoals
* `∃` (Exists): prepares the goal to provide a witness

```lean
example (p q : Prop)
        (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq
  /- the symbol · is syntax for "fill in the current subgoal"
  it makes goal structure explicit, the proof will not be affected if removed. -/
```

## 7. Natural Numbers

In Lean 4, natural numbers are defined inductively, forming the foundation for arithmetic proofs. This section covers the definition, core axioms, basic operations, and fundamental theorems essential for proving properties about numbers.

### 7.1 Inductive Definition

The set of natural numbers ($\mathbb{N}$) is defined as an inductive type with two constructors: a base case and a successor function.

```lean
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
````

* **`zero`**: Represents the number $0$.
* **`succ`**: Represents the successor function; `succ n` corresponds to $n + 1$.

**Intuition:** Every natural number is either `0` or the successor of another natural number.

### 7.2 The Peano Axioms

The inductive definition of `Nat` in Lean satisfies the Peano axioms, which characterize the natural numbers:

* **Zero exists:** $0 \in \mathbb{N}$.
* **Successor:** For every $n \in \mathbb{N}$, there is a successor $S(n) \in \mathbb{N}$.
* **Injectivity:** The successor function is injective.
  If $S(n) = S(m)$, then $n = m$.
* **Disjointness:** Zero is not the successor of any natural number:
  $\forall n,; S(n) \neq 0$.
* **Induction:**
  If a property $P$ holds for $0$, and
  if $P(n) \Rightarrow P(S(n))$ for all $n$,
  then $P$ holds for all natural numbers.

### 7.3 Basic Operations

Standard arithmetic operations are defined recursively on the structure of `Nat`.

#### Addition (`Nat.add`)

Defined by recursion on the second argument:

* $n + 0 = n$
* $n + \text{succ } m = \text{succ } (n + m)$

#### Multiplication (`Nat.mul`)

Defined as repeated addition:

* $n * 0 = 0$
* $n * \text{succ } m = n * m + n$

#### Power (`Nat.pow`)

Defined as repeated multiplication:

* $n^0 = 1$
* $n^{\text{succ } m} = (n^m) * n$

### 7.4 Fundamental Theorems

These theorems are frequently used in proofs to rewrite terms into canonical forms.

#### Associativity

Allows regrouping of operations.

```lean
Nat.add_assoc (a b c : Nat) : (a + b) + c = a + (b + c)
Nat.mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c)
```

#### Commutativity

Allows swapping the order of operands.

```lean
Nat.add_comm (a b : Nat) : a + b = b + a
Nat.mul_comm (a b : Nat) : a * b = b * a
```

#### Identity & Zero Properties

**Additive identity:** $0$

```lean
Nat.add_zero (n : Nat) : n + 0 = n
Nat.zero_add (n : Nat) : 0 + n = n
```

**Multiplicative identity:** $1$

```lean
Nat.mul_one (n : Nat) : n * 1 = n
Nat.one_mul (n : Nat) : 1 * n = n
```

**Zero property of multiplication:**

```lean
Nat.mul_zero (n : Nat) : n * 0 = 0
Nat.zero_mul (n : Nat) : 0 * n = 0
```

#### Distributivity

Connects addition and multiplication.

**Left distributivity:**

```lean
Nat.mul_add (a b c : Nat) : a * (b + c) = a * b + a * c
```

**Right distributivity:**

```lean
Nat.add_mul (a b c : Nat) : (a + b) * c = a * c + b * c
```

### 7.5 Useful Tactics for `Nat`

* **`simp`**
  Automatically simplifies goals using lemmas marked with the `@[simp]` attribute (e.g. `Nat.add_zero`).

* **`rw` (rewrite)**
  Manually applies specific theorems to transform the goal or hypotheses, e.g.

  ```lean
  rw [Nat.add_comm]
  ```

* **`ac_rfl`**
  Proves equalities up to associativity and commutativity.

* **`ring`**
  Solves equalities in commutative semirings and rings, handling associativity, commutativity, and distributivity automatically.

* **`linarith`**
  Solves goals involving linear arithmetic inequalities.

### 7.6 Examples
Example of using **`simp`** with `Nat` properties:
```lean
example (a b c : Nat) : a + b + c = b + (a + c) := by
  -- reassociate and commute to match the RHS
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
```
Example of using **`rw`** with `Nat` properties:
```lean
example (a b c : Nat) : a + (b + c) = b + (a + c) := by
  rw [Nat.add_assoc]
  rw [Nat.add_comm a b]
  rw [← Nat.add_assoc]
```
Example of using **`linarith`**:
```lean
example (x y : Nat) (h1 : x + y = 10) (h2 : x ≥ 7) : y ≤ 3 := by
  linarith
```
Example of using **`ring`**:
```lean
example (a b : Nat) : (a + b) * (a + b) = a*a + 2*a*b + b*b := by
  ring
```