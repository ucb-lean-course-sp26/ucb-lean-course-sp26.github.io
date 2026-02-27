import Mathlib.Tactic

/-
Lecture 3: Proof by induction and Proofs with Structure

Solutions to in-class demo exercises.
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
  simp

example (a : Nat) : 0 + a = a := by
  simp

example (a : Nat) : a * 1 = a := by
  rw [Nat.mul_one]

example (a : Nat) : 1 * a = a := by
  simp

/-!
## Rewriting demos with `rw`
-/

example (a b c : Nat) : (a + b) + c = a + (b + c) := by
  -- rewriting by associativity
  rw [Nat.add_assoc]

example (a b : Nat) : a + b = b + a := by
  -- rewriting by commutativity
  rw [Nat.add_comm]

example (a b c : Nat) : a * (b + c) = a*b + a*c := by
  -- distributivity (`Nat.mul_add`)
  rw [Nat.mul_add]

example (a b c : Nat) : (a + b) * c = a*c + b*c := by
  -- distributivity (`Nat.add_mul`)
  rw [Nat.add_mul]

/-!
## Using hypotheses with `rw` / `simp`
-/

example (x y z : Nat) (h : x = y) : x + z = y + z := by
  -- rewrite the goal using h
  rw [h]

example (x y z : Nat) (h : x = y) : z + x = z + y := by
  simp [h]

example (a b c : Nat) : a + b + c = b + (a + c) := by
  -- reassociate and commute to match the RHS
  linarith

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
  simp

example (n : Nat) : 0 + n = n := by
  -- demo: `simp` after `induction`
  simp

example (n : Nat) : n * 1 = n := by
  simp

example (n : Nat) : 1 * n = n := by
  simp

/-!
## Induction + rewriting: a small "algebraic" induction
-/

example (n : Nat) : n + n = 2 * n := by
  -- demo: induction + `simp` / `ring`
  ring


/-!
## Summation formula

Mathlib's `Finset.range (n+1)` is `{0,1,2,...,n}`.
So this states: 0 + 1 + ... + n = n*(n+1)/2.
-/

open scoped BigOperators

example (n : Nat) : (∑ i ∈ Finset.range (n + 1), i) * 2 = n * (n + 1) := by
  -- demo: `induction n with`
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hsum :
      (∑ i ∈ Finset.range (n + 2), i) = (∑ i ∈ Finset.range (n + 1), i) + (n+1) := by
      simp [Finset.sum_range_succ]
    simp [hsum, Nat.add_mul, ih]
    ring
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
  induction t with
  | leaf =>
    simp [leaves, internals]
  | node t1 t2 ih1 ih2 =>
    simp [leaves, internals, ih1, ih2]
    ring
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
  constructor
  · exact hP
  · exact hQ

example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.2

/-!
## Disjunction (∨)
To prove a disjunction, choose a side.
To use it, do case analysis.
-/

example (P Q : Prop) (hP : P) : P ∨ Q := by
  left
  exact hP

example (P Q : Prop) (h : P ∨ Q) : (¬ P → Q) := by
  intro notP
  cases h with
  | inl hP =>
    contradiction
  | inr hQ =>
    exact hQ

/-!
## Negation and contradiction
Recall: ¬P is defined as P → False.
-/

example (P : Prop) (h : P) : ¬¬P := by
  intro hnp
  apply hnp
  exact h

/-!
Proof by contradiction using classical logic.
-/

example (x : Nat) : x = 0 ∨ x ≠ 0 := by
  by_cases h : x = 0
  · left
    exact h
  · right
    exact h
/-!
## Existential quantifier (∃)
To prove ∃ x, P x, give a witness and a proof.
-/

example : ∃ n : Nat, n + 1 = 5 := by
  refine ⟨4, by simp⟩


/-!
## Universal quantifier (∀)
-/

example : ∀ n : Nat, n + 0 = n := by
  intro n
  simp

example (h : ∀ n, n < 10) : 12 < 10 := by
  specialize h 12
  exact h

/-!
## Bi-implication (↔)
To prove P ↔ P, prove both directions.
-/

example (P : Prop) : P ↔ P := by
  refine ⟨?_, by intro h; exact h⟩
  intro h
  exact h

example (a : Nat) : (a = 0) ↔ (a ≤ 0) := by
  refine ⟨?_, ?_⟩
  intro h
  simp [h]
  intro hale0
  exact le_antisymm hale0 (Nat.zero_le _)


/-!
## Uniqueness (∃!)
`∃! x, P x` is "there exists exactly one x such that P x".
-/

example : ∃! n : Nat, n = 0 := by
  refine ⟨0, rfl, ?_⟩
  intro y hy
  exact hy


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
  refine ⟨run M q w, rfl, ?_⟩
  intro q' hq'
  exact hq'
