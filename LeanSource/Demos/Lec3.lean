import Mathlib.Tactic

/-
Lecture 3: Proof by induction and Proofs with Structure

This file is for live demonstration.
All examples are included, but all proofs are left as `sorry`
so we can develop them interactively during lecture.
-/

/-!
# Part A: Nat proofs (simp / rw / ring / linarith)

Goal: get comfortable rewriting and simplifying arithmetic statements on `Nat`.

Some common lemmas (we'll use them via `simp` / `rw`):
- `Nat.add_assoc`, `Nat.mul_assoc`
- `Nat.add_comm`, `Nat.mul_comm`
- `Nat.add_zero`, `Nat.zero_add`
- `Nat.mul_one`, `Nat.one_mul`
- `Nat.mul_add`, `Nat.add_mul`

Tactics highlighted:
- `simp` : simplifies using rewriting rules (and your provided lemmas)
- `rw`   : rewrite using a lemma/hypothesis
- `ring` : normalizes polynomial-like expressions (commutative semiring reasoning)
- `linarith` : linear arithmetic reasoning (works well with equalities/inequalities)
-/

/-!
## Basic simp demos
-/

example (a : Nat) : a + 0 = a := by
  sorry

example (a : Nat) : 0 + a = a := by
  sorry

example (a : Nat) : a * 1 = a := by
  sorry

example (a : Nat) : 1 * a = a := by
  sorry

/-!
## Rewriting demos with `rw`
-/

example (a b c : Nat) : (a + b) + c = a + (b + c) := by
  -- rewriting by associativity
  sorry

example (a b : Nat) : a + b = b + a := by
  -- rewriting by commutativity
  sorry

example (a b c : Nat) : a * (b + c) = a*b + a*c := by
  -- distributivity (`Nat.mul_add`)
  sorry

example (a b c : Nat) : (a + b) * c = a*c + b*c := by
  -- distributivity (`Nat.add_mul`)
  sorry

/-!
## Using hypotheses with `rw` / `simp`
-/

example (x y z : Nat) (h : x = y) : x + z = y + z := by
  -- rewrite the goal using h
  simp [h]

example (x y z : Nat) (h : x = y) : z + x = z + y := by
  simp [h]

example (a b c : Nat) : a + b + c = b + (a + c) := by
  -- reassociate and commute to match the RHS
  simp [Nat.add_comm, Nat.add_left_comm]

example (a b c : Nat) : a + b + c = b + (a + c) := by
  rw [Nat.add_comm a b]
  rw [Nat.add_assoc]

/-!
## Algebra normalization with `ring`
-/

example (a b : Nat) : (a + b) * (a + b) = a*a + a*b + b*a + b*b := by
  ring

example (a b : Nat) : (a + b) * (a + b) = a*a + 2*a*b + b*b := by
  ring

/-!
## Linear arithmetic with `linarith`
-/

example (x y : Nat) (h1 : x + y = 10) (h2 : x ≥ 7) : y ≤ 3 := by
  linarith


/-!
# Part A2: Proof by induction

We now practice induction on:
1. Natural numbers (`Nat.rec` / `induction n with ...`)
2. Recursive data types (binary trees)

All proofs are left as `sorry` for live demo.
-/

/-!
## Induction on Nat: very simple examples
-/

example (n : Nat) : n + 0 = n := by
  -- demo: `induction n with`
  sorry

example (n : Nat) : 0 + n = n := by
  -- demo: `simp` after `induction`
  sorry

example (n : Nat) : n * 1 = n := by
  sorry

example (n : Nat) : 1 * n = n := by
  sorry

/-!
## Induction + rewriting: a small “algebraic” induction
-/

example (n : Nat) : n + n = 2 * n := by
  -- demo: induction + `simp` / `ring`
  sorry

/-!
## Summation formula

Mathlib's `Finset.range (n+1)` is `{0,1,2,...,n}`.
So this states: 0 + 1 + ... + n = n*(n+1)/2.
-/

open scoped BigOperators

example (n : Nat) : (∑ i ∈ Finset.range (n + 1), i) * 2 = n * (n + 1) := by
  -- demo: `induction n with`
  sorry

/-!
## Induction on binary trees
-/

inductive myTree where
  | leaf : myTree
  | node : myTree → myTree → myTree

namespace myTree

def leaves : myTree → Nat
  | leaf => 1
  | node t₁ t₂ => leaves t₁ + leaves t₂

def internals : myTree → Nat
  | leaf => 0
  | node t₁ t₂ => internals t₁ + internals t₂ + 1

/-!
### Main induction theorem on trees
-/

theorem leaves_eq_internals_add_one (t : myTree) :
    leaves t = internals t + 1 := by
  -- demo: `induction t with`
  -- leaf case is trivial
  -- node case uses the IHs
  sorry

end myTree


/-!
# Part B: Proofs with Structure (logic)

Now we switch to `Prop` proofs with tactics like `constructor`, `cases`, `intro`, etc.
-/

/-!
## Conjunction (∧)
A proof of `P ∧ Q` consists of a proof of `P` and a proof of `Q`.
-/

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  sorry

example (P Q : Prop) (h : P ∧ Q) : Q := by
  sorry

/-!
## Disjunction (∨)
To prove a disjunction, choose a side.
To use it, do case analysis.
-/

example (P Q : Prop) (hP : P) : P ∨ Q := by
  sorry

example (P Q : Prop) (h : P ∨ Q) : (¬ P → Q) := by
  sorry

/-!
## Negation and contradiction
Recall: ¬P is defined as P → False.
-/

example (P : Prop) (h : P) : ¬¬P := by
  sorry

/-!
Proof by contradiction using classical logic.
-/

example (x : Nat) : x = 0 ∨ x ≠ 0 := by
  sorry

/-!
## Existential quantifier (∃)
To prove ∃ x, P x, give a witness and a proof.
-/

example : ∃ n : Nat, n + 1 = 5 := by
  sorry

example (P : Nat → Prop) (h : ∃ x, P x) : True := by
  sorry

/-!
## Universal quantifier (∀)
-/

example : ∀ n : Nat, n + 0 = n := by
  sorry

example (h : ∀ n, n < 10) : 3 < 10 := by
  sorry

/-!
## Bi-implication (↔)
To prove P ↔ P, prove both directions.
-/

example (P : Prop) : P ↔ P := by
  sorry

example (a : Nat) : (a = 0) ↔ (a ≤ 0) := by
  sorry

/-!
## Uniqueness (∃!)
`∃! x, P x` is "there exists exactly one x such that P x".
-/

example : ∃! n : Nat, n = 0 := by
  sorry

/-!
## Deterministic Finite Automata (DFA)
-/

structure DFA (α : Type) where
  State  : Type
  start  : State
  step   : State → α → State
  accept : State → Bool

def run {α : Type} (M : DFA α) : M.State → List α → M.State
| q, []     => q
| q, a::w  => run M (M.step q a) w

def accepts {α : Type} (M : DFA α) (w : List α) : Bool :=
  M.accept (run M M.start w)

/-!
A tiny alphabet.
-/

inductive Bit where
  | O | I
deriving Repr, DecidableEq

open Bit

/-!
DFA accepting words that end with I.
-/

def endsWithI : DFA Bit :=
{ State  := Bool
, start  := false
, step   := fun _ b =>
    match b with
    | O => false
    | I => true
, accept := fun st => st
}

#eval accepts endsWithI [O, I, O, I]
#eval accepts endsWithI [I, O]
#eval accepts endsWithI []

/-!
DFA accepting words with an even number of I's.
-/

def evenIs : DFA Bit :=
{ State  := Bool
, start  := false
, step   := fun st b =>
    match b with
    | O => st
    | I => !st
, accept := fun st => !st
}

#eval accepts evenIs []
#eval accepts evenIs [I, I]
#eval accepts evenIs [O, I, O, I]
#eval accepts evenIs [I, O, O]

/-!
## Determinism as uniqueness
-/

theorem run_deterministic
  {α : Type} (M : DFA α) (q : M.State) (w : List α) :
  ∃! q' : M.State, q' = run M q w := by
  sorry
