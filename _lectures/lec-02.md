---
layout: lecture
title: "Lecture 2: Terms vs Tactics, More Tactics, Induction"
date: 2026-01-30
slides_url: https://docs.google.com/presentation/d/1WIge349l2xBoukGcT9VLx6dk6j2EnJVILSJFvKL2pWA/edit?usp=sharing
demo_url: https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fucb-lean-course-sp26%2Fucb-lean-course-sp26.github.io%2Frefs%2Fheads%2Fmain%2FLeanSource%2FDemos%2FLec2.lean
demo_sol_url: https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fucb-lean-course-sp26%2Fucb-lean-course-sp26.github.io%2Frefs%2Fheads%2Fmain%2FLeanSource%2FDemos%2FLec2sol.lean
---

* TOC
{:toc}

## 1. Term Mode vs. Tactic Mode

In Lean, we can construct proofs and definitions in two primary ways:
* **Term Mode** (functional programming style), and
* **Tactic Mode** (imperative command style).

### Propositions as Types

Recall from Lecture 1, that in Lean, propositions are types. That is, when we
write `p : Prop`, it means that `p` is a "type".

We say that "`p` is True" or "`p` holds" if there exists an object `h` of type
`p` (written `h : p`). So, demonstration of an object of type `p` is synonymous
with a "proof of `p`".

Such objects are constructed by using constructors. For example, let's take the
example of how _equality_ is defined in Lean (see
[source](https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean#L275-L278)).
`a = b`, or equivalently `Eq a b` is always a type (an instance of `Prop`) for
any `a b : α`. The constructor `Eq.refl` constructs objects of type `Eq a a`,
but there is no constructor that constructs objects of type `Eq a b` when `a`
and `b` are not the same.

### Modus Ponens

We illustrates this with the *Modus Ponens* example (if $p \rightarrow q$ and
$p$, then $q$).

**Term Mode:**
We treat the proof as a function application. If `f : p → q` is a function
mapping terms of type `p` to terms of type `q` and `hp` is a term of type `p`,
applying `f` to `hp` (`f hp`) produces a term of type `q`.

```lean
theorem mp1 (p q : Prop) (f : p → q) (hp : p) : q := f hp
```

**Tactic Mode:**
We use a `by` block to enter the _tactic mode_. We instruct Lean step-by-step on
how to construct the proof.

Once `by` is written, we enter the goal state
`(p q : Prop) (f : p → q) (hp : p) ⊢ q`

Lean knows that we are trying to construct an object of type `q`.

`apply f`: Tells Lean to use the implication `p → q`. The goal changes from
seeking `q` to seeking `p`.
 
`exact hp`: Tells Lean to use the hypothesis `hp` to satisfy the goal `p`.

```lean
theorem mp1' (p q : Prop) (f : p → q) (hp : p) : q := by
  apply f
  exact hp
```

Using `#print mp1` or `#print mp1'`, we can see that their internal definitions
are exactly identical, namely,
`theorem mp1 : ∀ (p q : Prop), (p → q) → p → q := fun p q f hp => f hp`

### Adding two numbers

While tactic mode is usually for theorems, it can also define data or functions.
The example below shows two equivalent ways to write a function for
adding two natural numbers in term mode and in tactic mode.

```lean
def addInTermMode (x y : Nat) : Nat := Nat.add x y  -- equivalently, x + y

def addInTacticMode (x y : Nat) : Nat := by
  apply Nat.add
  exact x
  exact y
```

## 2. Interacting with Lean: #check, #eval, #print

Three commands are essential for inspecting terms and types:

1. **`#check` ("What is its type?")**
  * Applied to any term `t` to display its type.
  * Example: `#check 5` or `#check List`.

2. **`#eval` ("What is its value?")**
  * Computes the result of an expression.
  * It cannot run on theorems or non-computable expressions (e.g. those
    involving real numbers).

3. **`#print` ("How is it defined?")**
  * Displays the internal structure or definition of a name.
  * It cannot be used on raw expressions like `2 + 3`.

## 3. Arithmetic and Logic Tactics

### Recap of Logic Tactics

In class, we reviewed several fundamental tactics through self-exercises; see
[demo]({{page.demo_url}}); these were borrowed from the
[course](https://yuvalfilmus.cs.technion.ac.il/courses/?crid=1777)
taught by Yuval Filmus.

Below is a summary of the different tactics and when they are applicable.

| **Tactic** | **Use when goal is...** | **Use when hypothesis `h` is...** |
| :--- | :--- | :--- |
| `intro` | `A → B`, `∀ x, P x`, `¬A` | - |
| `apply h`| Matches conclusion of `h` | `A → B`, `∀ x, P x` |
| `exact h`| Exactly `h` | matches goal |
| `assumption`| *(matches any hyp)* | - |
| `constructor`| `A ∧ B`, `A ↔ B` | - |
| `cases h` | - | `A ∧ B`, `A ∨ B`, `∃ x, P x`, `False` |
| `left`/`right`| `A ∨ B` | - |
| `use y` | `∃ x, P x` | - |
| `rfl` | `a = a` | - |

### Arithmetic Automation

Mathlib provides powerful tactics for handling numbers. These tactics
automatically construct proofs when the target goal involves standard
derivations using linear arithmetic or polynomial identities.

| Tactic | Domain | Description |
| --- | --- | --- |
| `omega` | ℕ | Solves linear constraints (Presburger arithmetic). |
| `linarith` | Rings (e.g. ℝ, ℚ)| Handles linear equalities and inequalities over fields/rings. |
| `ring` | Rings (e.g. ℝ, ℚ) | Proves polynomial identities. |

Below we provide simple examples using these tactics.

```lean
theorem omega_ex (n : ℕ) : (n - 5) + 5 ≥ n := by
  omega

theorem linarith_ex (x y : ℚ) (h1 : 2 * x < y) (h2 : y < 10) : x < 5 := by
  linarith

theorem ring_ex (a b : ℤ) : (a + b) * (a - b) = a^2 - b^2 := by
  ring
```

It is instructive to see the proof generated by Lean behind the scenes, using
`#print omega_ex`, `#print linarith_ex` and `#print ring_ex`.

## 4. The calc Tactic

The `calc` block is used to structure proofs involving chains of relations
(equality, inequality, divisibility) to improve readability.

**Example:**
Instead of nesting multiple `apply` tactics (like `lt_of_le_of_lt` and
`le_of_le_of_eq`), `calc` allows a linear presentation:

```lean
example (a b c d : Nat) (h1 : a ≤ b) (h2 : b = c) (h3 : c < d) : a < d :=
  calc
    a ≤ b := h1
    _ = c := h2
    _ < d := h3
```

It also supports arbitrary relations like "divides" (`∣`, typed as `\|`) or
operations on Reals.

```lean
example (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  calc
    a ∣ b := h1
    _ ∣ c := h2
```

Below is an example borrowed from Heather Macbeth's book
[The Mechanics of Proof](https://hrmacbeth.github.io/math2001/01_Proofs_by_Calculation.html#id11)

```lean
example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by ring
```

## 5. Inductive Types

Inductive types allow us to define custom data structures. A simple inductive
type lists all possible values (constructors), e.g. we define an inductive type
for all days of the week. (Example borrowed from this
[talk](https://www.youtube.com/watch?v=S-aGjgIDQZY) by Leonardo de Moura.)

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

### Pattern Matching (`match`)

We define functions on inductive types using `match ... with`. Below we
provide examples of the same, by defining functions computing the next day and
the previous day.

```lean
namespace Day
  /-- Next day of the week. -/
  def next (day : Day) : Day :=
    match day with
    | sunday => monday
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => saturday
    | saturday => sunday

  /-- Previous day of the week. -/
  def previous (day : Day) : Day :=
    match day with
    | sunday => saturday
    | monday => sunday
    | tuesday => monday
    | wednesday => tuesday
    | thursday => wednesday
    | friday => thursday
    | saturday => friday
end Day
```

### Proofs by Cases (`cases`)

To prove a theorem about an enumerated type, we use the `cases` tactic. This
splits the goal into subgoals—one for each constructor.

```lean
theorem nextPreviousIsToday (d : Day) : d.next.previous = d := by
  cases d   -- Now there are 7 subgoals.
  rfl
  rfl
  rfl
  rfl
  rfl
  rfl
  rfl
```

If the same tactic is to applied to each case, we can use `<;>` as follows:

```lean
theorem nextPreviousIsToday' (d : Day) : d.next.previous = d := by
  cases d <;> rfl  -- Apply the same tactic for all sub-goals.
```

`cases` can also derive `False` from empty propositions.

```lean
example : Day.sunday ≠ Day.monday := by
  intro h    -- h : Day.sunday = Day.monday ⊢ False
  cases h    -- h is already false by "disjoint constructors".
```

### Proofs by Induction (`induction`)

Let us first define an inductive type that is recursively defined, such as a
Binary Tree, which is either empty (a.k.a. "leaf"), or has a value associated
to the root node, and has a left and right sub-tree.

```lean
inductive BinTree where
  | empty : BinTree
  | node (val : Nat) (left : BinTree) (right : BinTree) : BinTree
```

We can define functions recursively on such types by calling the function on
sub-structures within.

```lean
def mirror (t : BinTree) : BinTree :=
  match t with
  | .empty => .empty
  | .node n l r => .node n (mirror r) (mirror l)
```

When proving properties of recursive structures, `cases` is often insufficient
because it does not provide an inductive hypothesis. We use `induction` instead.

```lean
/-- Mirroring twice returns the original tree. -/
theorem mirror_mirror (t : BinTree) : mirror (mirror t) = t := by
  induction t with
  | empty =>
    rfl
  | node n l r ih_l ih_r =>
    -- We get inductive hypotheses ih_l and ih_r
    dsimp [mirror]
    rw [ih_l, ih_r]
```

Here, `ih_l` assumes the theorem holds for the left subtree, and `ih_r` assumes
it holds for the right subtree.