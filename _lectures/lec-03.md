---
layout: lecture
title: "Lecture 2: Terms vs Tactics, More Tactics, Induction"
date: 2026-02-06
slides_url: https://docs.google.com/presentation/d/1qkxnjoUbJ3frbNTJh1Os7FW8QLmYJx-NmEo8nGwaslI/edit?usp=sharing
demo_url: https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fucb-lean-course-sp26%2Fucb-lean-course-sp26.github.io%2Frefs%2Fheads%2Fmain%2FLeanSource%2FDemos%2FLec3.lean
---

* TOC
{:toc}

## 1\. Introduction

In the previous lectures, we learned the basic syntax of Lean and how to write simple definitions and theorems.
Now we begin learning **how to build structured mathematical proofs** using Lean's tactic framework.

This lecture focuses on logical connectives and quantifiers:

| Concept     | Symbol    | Lean Tactics                                |
| ----------- | --------- | --------------------------------------------- |
| Conjunction | ∧         | `constructor`, `cases`                        |
| Disjunction | ∨         | `left`, `right`, `cases`                      |
| Negation    | ¬P        | `intro`, `by_contra`                          |
| Implication | P → Q     | `intro`, `apply`                              |
| Existential | ∃ x, P x  | `exists`, `cases`, `refine`                   |
| Universal   | ∀ x, P x  | `intro`, `specialize`                         |
| Iff         | P ↔ Q     | `constructor`, `apply`, `have`                |
| Uniqueness  | ∃! x, P x | pair of existence + uniqueness, `refine`      |


These are the building blocks of all later work in TCS formalization.


## 2\. Conjunction (∧)

A conjunction proof `P ∧ Q` contains **two components**: a proof of `P` and a proof of `Q`.

### Constructing a conjunction

```lean
example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ
```

### Using a conjunction

We can extract the components using `cases`.

```lean
example (P Q : Prop) (h : P ∧ Q) : Q := by
  cases h with
  | intro hP hQ => 
      exact hQ
```



## 3\. Disjunction (∨)

To prove a disjunction, choose the appropriate side.

```lean
example (P Q : Prop) (hP : P) : P ∨ Q := by
  left
  exact hP
```

Using a disjunction:

```lean
example (P Q : Prop) (h : P ∨ Q) : (¬P → Q) := by
  intro hnotP
  cases h with
  | inl hP => contradiction
  | inr hQ => exact hQ
```

## 4\. Negation and Contradiction

Negation is defined as:

```lean
¬P  :=  P → False
```

To prove ¬P:

```lean
example (P : Prop) (h : P) : ¬¬P := by
  intro hnp
  apply hnp
  exact h
```

### Proof by contradiction: `by_contra`

```lean
example (x : Nat) : x = 0 ∨ x ≠ 0 := by
  -- Proof by contradiction using classical logic.
  classical

  by_contra h
  -- Now h : ¬(x = 0 ∨ x ≠ 0)

  -- obtain a decidable instance for (x = 0)
  -- classical logic and Decidable will be discussed later this lecture
  have hx : Decidable (x = 0) := inferInstance

  cases hx with
  | isTrue hx0 =>
      apply h
      left
      exact hx0
  | isFalse hx0 =>
      apply h
      right
      exact hx0
```

## 5\. Existential Quantifiers (∃)

To prove `∃ x, P x`, we provide a witness and a proof.

```lean
example : ∃ n : Nat, n + 1 = 5 := by
  exists 4
```

Using an existential:

```lean
example (P : Nat → Prop) (h : ∃ x, P x) : True := by
  cases h with
  | intro x hx =>
      trivial
```

## 6. Universal Quantifiers (∀)

To prove a universal statement, introduce an arbitrary variable.

```lean
example : ∀ n : Nat, n + 0 = n := by
  intro n
  simp
```

To use a universal statement:

```lean
example (h : ∀ n, n < 10) : 3 < 10 := by
  specialize h 3
  exact h
```

## 7\. Bi-implication (↔)

To prove `P ↔ P`, prove each direction.

```lean
example (P : Prop) : P ↔ P := by
  constructor
  · intro hPf
    sorry
  · intro hPb
    sorry
```

A more concrete version:

```lean
example (a : Nat) : (a = 0) ↔ (a ≤ 0) := by
  constructor
  · intro h; simp [h]
  · intro h; exact le_antisymm h (Nat.zero_le _)
```

Here is a polished, lecture-quality subsection with a smoother flow, corrected LaTeX, and the example placed first. All math displays now compile correctly in Markdown.

---

Understood — here is your subsection **with your LaTeX left exactly as written**, and with a concise explanation of `refine` added in the correct place.
Nothing in your math blocks or LaTeX has been changed.

---

## 8. Uniqueness (`∃!`)

A statement of the form `∃! x, P x` means:

1. **Existence:** there is some `x` with `P x`
2. **Uniqueness:** if `P x` and `P y`, then `x = y`

Lean defines `∃! x, P x` as:

$$\exists\, x,\; P(x)\;\land\;\forall y,\; P(y) \rightarrow y = x.$$

---

### Example

```lean
example : ∃! n : ℕ, n = 0 := by
  refine ⟨0, rfl, ?_⟩
  intro y hy
  simp [hy]
```

---

### What `refine` Does

The `refine` tactic allows you to *partially construct* the final term of a goal.
It accepts a term that may contain placeholders (`?_`) and generates new subgoals for each missing piece.

For `∃!`, Lean expects three components:

1. a witness `n`,
2. a proof that `P n` holds,
3. a proof that any `y` satisfying `P y` must equal `n`.

The line

```lean
refine ⟨0, rfl, ?_⟩
```

fills in the first two components (`0` and `rfl`) and leaves the third as a new goal.
This is why `refine` is the natural tool for `∃!`, whose definition is a triple of data.

---

### Understanding Lean’s Uniqueness Goal

Running the example produces a uniqueness goal of the form:

```lean
∀ (y : ℕ), (fun n => n = 0) y → y = ?w
```

This goal looks complicated, but each part has a simple meaning:

* `(fun n => n = 0) y` is just Lean’s internal way of writing the predicate `y = 0`.
  Lean uses this functional form because the definition of `∃!` contains a lambda expression.
* `?w` is a metavariable representing the **witness** you supplied earlier using
  `refine ⟨w, hw, ?_⟩`. Lean will later fill this with `0`.

Thus the goal is logically equivalent to:

$$\forall y \in \mathbb{N}, (y = 0) \to (y = w).$$


After Lean resolves `?w = 0`, the goal becomes:


$$\forall y,\; y = 0 \to y = 0.$$

This is discharged by rewriting with the hypothesis:

```lean
intro y hy
simp [hy]
```

This completes the uniqueness part:
**any number satisfying the predicate must be the same as the chosen witness.**

---

## 9. Example: Deterministic Automata

### Deterministic Automata: Acceptance Is Deterministic

A **deterministic finite automaton (DFA)** has exactly one possible transition from any state on any input symbol.
As a consequence:

> **Fact.** For any input string, a DFA has a *unique run*.
> Therefore, if a DFA accepts a string, the accepting run is unique.

This is the simplest setting in which we can later talk about uniqueness (`∃!`) in a concrete, computational way.

---

### Defining a DFA in Lean

We represent a DFA as a structure consisting of:

* a type of states,
* a start state,
* a deterministic transition function,
* and a Boolean acceptance test.

```lean
/-- A tiny deterministic finite automaton (DFA). -/
structure DFA (α : Type) where
  State  : Type
  start  : State
  step   : State → α → State
  accept : State → Bool
```

Here `α` is the **alphabet type**, and `State` is an arbitrary type representing the DFA’s internal states.

---

### Running a DFA

To process an input word, we recursively apply the transition function symbol by symbol.

```lean
/-- Run the DFA on a word. -/
def run {α : Type} (M : DFA α) : M.State → List α → M.State
| q, []      => q
| q, a :: w  => run M (M.step q a) w
```

* On the empty input `[]`, the DFA stays in the current state.
* On `a :: w`, it takes one deterministic step and continues recursively.

Because the transition function is deterministic, this run is **unique**.

---

### Acceptance

A word is accepted if the final state reached by `run` is accepting.

```lean
/-- Does the DFA accept the word? -/
def accepts {α : Type} (M : DFA α) (w : List α) : Bool :=
  M.accept (run M M.start w)
```

This is a *computable* notion of acceptance: it returns a `Bool`.

---

### A Tiny Alphabet

We now define a minimal alphabet with two symbols.

```lean
inductive Bit where
  | O | I
deriving Repr, DecidableEq
```

Opening the namespace lets us write `O` and `I` instead of `Bit.O` and `Bit.I`.

```lean
open Bit
```

---

### Example 1: Words That End with `I`

This DFA remembers **only the last symbol read**.

```lean
/-- Accepts exactly the words that end with `I`. -/
def endsWithI : DFA Bit :=
{ State  := Bool
, start  := false
, step   := fun _ b =>
    match b with
    | O => false
    | I => true
, accept := fun st => st
}
```

* The state is a `Bool` indicating whether the last symbol was `I`.
* Reading `O` always moves to `false`.
* Reading `I` always moves to `true`.

Example evaluations:

```lean
#eval accepts endsWithI [O, I, O, I]  -- true
#eval accepts endsWithI [I, O]        -- false
#eval accepts endsWithI []            -- false
```

---

### Example 2: Words with an Even Number of `I`

This DFA tracks the **parity** of how many `I`s have been seen so far.

```lean
/-- DFA that accepts words with an even number of `I`. -/
def evenIs : DFA Bit :=
{ State  := Bool          -- false = even, true = odd
, start  := false
, step   := fun st b =>
    match b with
    | O => st
    | I => !st
, accept := fun st => !st
}
```

* Reading `I` toggles the state.
* Reading `O` leaves the state unchanged.
* Acceptance means ending in the “even” state.

Example evaluations:

```lean
#eval accepts evenIs []                -- true
#eval accepts evenIs [I, I]            -- true
#eval accepts evenIs [O, I, O, I]      -- true
#eval accepts evenIs [I, O, O]         -- false
```

---

## 10. DFA’s computation is fully determined by its input
```lean
theorem run_deterministic {α : Type} (M : DFA α) (q : M.State) (w : List α) :
  ∃! q' : M.State, q' = run M q w := by
  refine ⟨run M q w, rfl, ?_⟩
  intro q' hq'
  simpa [hq']
```

---

### 1. What does `∃!` *mean* in Lean?

In Lean,

```lean
∃! x, P x
```

is **definitionally** shorthand for:

> There exists an `x` such that `P x`,
> and for any `y`, if `P y` holds, then `y = x`.

Formally (simplified):

```lean
∃ x, P x ∧ ∀ y, P y → y = x
```

So a proof of `∃! x, P x` has **three parts**:

1. A witness `x`
2. A proof that `P x` holds
3. A proof that any other `y` satisfying `P y` equals `x`

---

### 2. What is our `P` here?

In our theorem:

```lean
∃! q' : M.State, q' = run M q w
```

The predicate is:

```lean
P q' := q' = run M q w
```

So we are saying:

> There is exactly one state equal to `run M q w`.

This is intentionally *trivial* — and that’s the point.
Determinism here comes from *function evaluation*, not from a deep argument.

---

### 3. The `refine ⟨ … ⟩` line

```lean
refine ⟨run M q w, rfl, ?_⟩
```

This is constructing the triple required by `∃!`.

#### Part 1: the witness

```lean
run M q w
```

We are saying:

> “The unique final state is `run M q w`.”

---

#### Part 2: existence proof

```lean
rfl
```

This proves:

```lean
run M q w = run M q w
```

which is exactly `P (run M q w)`.

So existence is done.

---

#### Part 3: uniqueness proof (the hard-looking part)

We are left with the goal:

```lean
⊢ ∀ q' : M.State, q' = run M q w → q' = run M q w
```

Lean replaces this with a `?_` placeholder, which we now fill.

---

### 4. Entering the uniqueness proof

```lean
intro q' hq'
```

This introduces:

* an arbitrary state `q'`
* a hypothesis `hq' : q' = run M q w`

So now the goal is:

```lean
⊢ q' = run M q w
```

But… that’s **exactly** what `hq'` already says.

---

### 5. The `simpa` line

```lean
simpa [hq']
```

This tells Lean:

> “Rewrite the goal using `hq'`, and it becomes trivial.”

Indeed, replacing `q'` by `run M q w` turns the goal into:

```lean
run M q w = run M q w
```

which Lean closes automatically.

---

### 6. One paragraph explanation

> To prove uniqueness (`∃!`) in Lean, we must give an explicit witness, prove it satisfies the property, and then prove that anything else satisfying the same property must be equal to it.
> For DFAs, determinism is trivial because the run function already computes a unique final state.


---

## 11\. Classical Logic, Constructive Logic, and `Decidable`

Lean is **constructive by default**, meaning it does not assume classical principles such as the law of excluded middle (`P ∨ ¬P`) unless they can be justified computationally.  
The mechanism that governs this behavior is the **`Decidable`** typeclass, which expresses whether Lean can *compute* whether a proposition is true or false.

Understanding this distinction is essential for structured proofs, especially when using tactics such as `by_cases`, `by_contra`, or reasoning about computability in TCS.

---

### The `Decidable` Typeclass

For any proposition `P : Prop`, Lean may have an instance of:

```lean
Decidable P
```

which is defined as:

```lean
inductive Decidable (P : Prop) : Type
| isTrue  : P → Decidable
| isFalse : (¬ P) → Decidable
```

So a value of type `Decidable P` contains:

1. a proof of `P`, or
2. a proof of `¬P`.

This is stronger than a Boolean—`Decidable` carries *logical evidence*.

Lean automatically provides `Decidable` instances for many propositions:

```lean
instance : Decidable (x = y)
instance : Decidable (n < m)
instance : Decidable (P ∧ Q)
instance : Decidable (P ∨ Q)
```

Thus, the following works constructively:

```lean
example (x : Nat) : x = 0 ∨ x ≠ 0 := by
  by_cases h : x = 0
  · left; exact h
  · right; exact h
```

because equality on naturals is decidable.

However, for an undecidable conjecture:

```lean
example : GoldbachConjecture ∨ ¬GoldbachConjecture := by
  by_cases h : GoldbachConjecture      -- ERROR: not decidable
```

Lean refuses unless classical logic is activated.

---

### Classical Logic in Lean

To enable classical reasoning, write:

```lean
classical
```

This imports a non-computable global instance:

```lean
instance (P : Prop) : Decidable P := Classical.decEq _
```

meaning:

> Under `classical`, *every* proposition is treated as decidable.

This unlocks:

* `by_cases h : P`
* `by_contra`
* `em : P ∨ ¬P`
* classical theorems relying on excluded middle or choice

Example:

```lean
example (P : Prop) : ¬¬P → P := by
  classical
  intro h
  by_contra hP
  apply h; exact hP
```

Without `classical`, the final step (`¬¬P → P`) is not constructively valid.

---

### Why This Matters in TCS

Constructive reasoning aligns naturally with computability:

* If `P` is decidable, we have an algorithm deciding it.
* Proofs become executable procedures.
* Lean can extract algorithms from constructive proofs.

Classical reasoning allows:

* non-constructive existence (e.g., diagonalization arguments),
* pigeonhole arguments,
* cardinality arguments,
* proofs involving infinitely many primes or undecidable problems.

Both styles appear frequently in TCS.
Explicitly controlling when you step into classical logic helps maintain the computational meaning of your proofs.

---

### Summary of Logical Worlds in Lean

| Mode             | Excluded Middle     | `by_cases` on arbitrary `P` | Computable? | How to Enable |
| ---------------- | ------------------- | --------------------------- | ----------- | ------------- |
| **Constructive** | Only when decidable | Only when `Decidable P`     | Yes         | Default       |
| **Classical**    | Always              | Always                      | No          | `classical`   |

When writing proofs, Lean makes you aware of which world you're in.
This clarity is especially valuable when reasoning about decision procedures, reductions, or undecidability results in theoretical CS.



## 12\. Exercises

### Exercise 1

Prove:

```lean
theorem my_and_comm (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  sorry
```

### Exercise 2

Show that for any relation `R`, if `R` is symmetric and transitive and there exists `x` with `R x y`, then `R y x`.


