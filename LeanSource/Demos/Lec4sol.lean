/-
In this file, we formalize notions of decision tree complexity and sensitivity
of Boolean functions over the Boolean hypercube.

This source could serve as a starting point for formalizing more definitions
and theorems in query complexity of Boolean functions. See below for an
introductory survey. Some of the open problems posed in the survey have been
resolved since!

Reference: Complexity measures and decision tree complexity: a survey
Authors: Harry Buhrman, Ronald de Wolf
Link: https://www.sciencedirect.com/science/article/pii/S030439750100144X
-/

import Mathlib
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Order.SetNotation

/- ---------------------- Boolean Inputs and Functions ---------------------- -/
section BooleanFunctions

/-- Boolean Input over n variables.
Encoding: `0` as `false`, and `1` as `true`.
-/
abbrev BoolInput (n : ℕ) := Fin n → Bool

/-- A Boolean function f : {0,1}^n → {0,1}.
Encoding: `0` as `false`, and `1` as `true`.
-/
abbrev BoolFn (n : ℕ) := BoolInput n → Bool

variable {n : ℕ}

-- Some example inputs
-- Defining an input as a function:
def x110 (i : Fin 3) : Bool :=
  match i with
  | 0 => true
  | 1 => true
  | 2 => false

-- Lean's syntactic sugar for defining terms of type `Fin n → α`.
def x000 := ![false, false, false]
def x001 := ![false, false, true]
def x010 := ![false, true, false]
def x011 := ![false, true, true]
def x100 := ![true, false, false]
def x101 := ![true, false, true]
def x111 := ![true, true, true]

/-- Hamming Weight: The number of 1s in the input x. -/
def hammingWeight (x : BoolInput n) : ℕ :=
  -- Fintype.card { i // x i = true }
  (Finset.univ.filter (fun i => x i = true)).card

#check hammingWeight
#eval hammingWeight x010  -- 1
#eval hammingWeight x110  -- 2
#eval hammingWeight x111  -- 3

-- Example functions: OR, AND, PARITY, MAJORITY

/-- OR Function: OR_n(x) = 1 iff |x| ≥ 1. -/
def OR (x : BoolInput n) : Bool :=
  hammingWeight x ≥ 1

/-- AND Function: AND_n(x) = 1 iff |x| = n. -/
def AND (x : BoolInput n) : Bool :=
  hammingWeight x = n

/-- Parity Function: PARITY_n(x) = 1 iff |x| is odd. -/
def PARITY (x : BoolInput n) : Bool :=
  (hammingWeight x) % 2 = 1

/-- Majority Function: MAJORITY_n(x) = 1 iff |x| > ⌊n/2⌋. -/
def MAJORITY (x : BoolInput n) : Bool :=
  hammingWeight x > n / 2

#eval OR x110
#eval AND x110
#eval PARITY x110
#eval MAJORITY x110

end BooleanFunctions

/- ---------------- (Deterministic) Decision Tree Complexity ---------------- -/
section DeterministicDecisionTree

variable {n : ℕ}

/-- Deterministic Decision Tree

A rooted ordered binary tree. Internal nodes are labeled with a variable
index (Fin n). Leaves are labeled with a value 0 or 1 (Bool).
-/
inductive DecisionTree (n : ℕ) where
  | leaf (val : Bool) : DecisionTree n
  | node (i : Fin n) (left : DecisionTree n) (right : DecisionTree n) : DecisionTree n

namespace DecisionTree

/-- Evaluation of Decision Tree

Given an input x, start at root. If leaf, return val.
If node labeled i, query x_i. If 0 (false), go left. If 1 (true), go right.
-/
def eval (t : DecisionTree n) (x : BoolInput n) : Bool :=
  match t with
  | DecisionTree.leaf val => val
  | DecisionTree.node i left right =>
      if x i then -- x_i = 1 (true)
        eval right x -- "if x_i=1 then recursively evaluate the right subtree"
      else -- x_i = 0 (false)
        eval left x  -- "if x_i=0 then recursively evaluate the left subtree"

/-- DecisionTree computes a function

A tree computes `f` if its evaluates to `f(x)` for all inputs `x`.
-/
def computes (t : DecisionTree n) (f : BoolFn n) : Prop :=
  ∀ x : BoolInput n, f x = t.eval x

/-- Depth of a DecisionTree

The number of queries made on the worst-case input.
This corresponds to the depth of the tree (0 for leaves).
-/
def depth (t : DecisionTree n) : ℕ :=
  match t with
  | DecisionTree.leaf _ => 0
  | DecisionTree.node _ left right => 1 + max (depth left) (depth right)

end DecisionTree

/-- Deterministic Decision Tree Complexity D(f)

The depth of an optimal (minimal-depth) decision tree that computes f.
We define this as the minimum of the set of depths of all trees computing f.
-/
noncomputable def DecisionTreeComplexity (f : BoolFn n) : ℕ :=
  sInf { d | ∃ t : DecisionTree n, t.computes f ∧ t.depth = d }
-- `noncomputable def` means that Lean does not attempt to compile this
-- definition into executable code.

end DeterministicDecisionTree

/-- Decision Tree for 2-bit And. -/
def AND2 : DecisionTree 2 :=
  .node 0
  (.leaf false)
  (.node 1 (.leaf false) (.leaf true))

#eval AND2.eval ![false, false]
#eval AND2.eval ![false, true]
#eval AND2.eval ![true, true]

/-- Decision Tree for 2-bit Parity. -/
def PARITY2 : DecisionTree 2 :=
  .node 0
  (.node 1 (.leaf false) (.leaf true))
  (.node 1 (.leaf true) (.leaf false))

#eval PARITY2.eval ![false, false]
#eval PARITY2.eval ![false, true]
#eval PARITY2.eval ![true, true]

/- ------------------------------ Sensitivity ------------------------------- -/
section Sensitivity

variable {n : ℕ}

/-- Flips the i-th bit of input x. -/
def flipBit (x : BoolInput n) (i : Fin n) : BoolInput n :=
  fun j => if j = i then !(x j) else x j

/-- The sensitivity of f at input x: number of neighbors with different function values. -/
def sensitivityAt (f : BoolFn n) (x : BoolInput n) : ℕ :=
  (Finset.univ.filter (fun i => f x ≠ f (flipBit x i))).card

/-- The sensitivity of Boolean function f. -/
def sensitivity (f : BoolFn n) : ℕ :=
  Finset.univ.sup (fun x => sensitivityAt f x)
  -- Note: This is equivalent to the following:
  -- Finset.sup Finset.univ (fun x => sensitivityAt f x)

end Sensitivity

#eval sensitivityAt AND2.eval ![false, false]  -- 0
#eval sensitivityAt AND2.eval ![false, true]   -- 1
#eval sensitivityAt AND2.eval ![true, true]    -- 2
#eval sensitivity AND2.eval                    -- 2
#eval sensitivityAt PARITY2.eval ![false, false]  -- 2

/- ----------------- Sensitivity ≤ Decision Tree Complexity ---------------- -/
section DecisionTreeVsSensitivity

variable {n : ℕ}

/-- Helper: The length of the path taken by input x -/
def pathLength (t : DecisionTree n) (x : BoolInput n) : ℕ :=
  match t with
  | .leaf _ => 0
  | .node i l r => 1 + if x i then pathLength r x else pathLength l x

/-- Lemma A: The path length is always bounded by the tree depth. -/
lemma pathLength_le_depth (t : DecisionTree n) (x : BoolInput n) :
  pathLength t x ≤ t.depth := by
  induction t with
  | leaf _ => rfl
  | node i l r ih_l ih_r =>
      unfold pathLength DecisionTree.depth
      by_cases h : x i
      · simp [h]
        right
        exact ih_r
      · simp [h]
        left
        exact ih_l

/-- Lemma B: Key Lemma.
    If t computes f, the sensitivity at specific input x is bounded by the path length. -/
lemma sensitivityAt_le_pathLength {t : DecisionTree n} {f : BoolFn n}
  (h_comp : t.computes f) (x : BoolInput n) :
  sensitivityAt f x ≤ pathLength t x := by
  induction t generalizing f with
  | leaf val =>
    unfold pathLength sensitivityAt
    unfold DecisionTree.computes DecisionTree.eval at h_comp
    simp [h_comp]
  | node i l r ih_l ih_r =>
    unfold pathLength
    by_cases hxi : x i = true
    · -- Case: Go Right
      simp [hxi]
      let g := r.eval
      have h_g_comp : r.computes g := fun _ => rfl
      specialize ih_r h_g_comp
      unfold sensitivityAt
      unfold sensitivityAt at ih_r
      let S_f := Finset.univ.filter (fun j => f x ≠ f (flipBit x j))
      let S_g := Finset.univ.filter (fun j => g x ≠ g (flipBit x j))
      have h_subset : S_f ⊆ S_g ∪ {i} := by sorry
      unfold S_f at h_subset
      unfold S_g at h_subset
      calc (Finset.univ.filter (fun i => f x ≠ f (flipBit x i))).card
      _ <= (Finset.univ.filter (fun i => g x ≠ g (flipBit x i))).card + 1 := by sorry
      _ ≤ 1 + pathLength r x := by linarith [ih_r]
    · -- Case: Go Left (Symmetric to above)
      let hxi_false := Bool.eq_false_of_not_eq_true hxi
      simp[hxi_false]
      sorry

/-- Sensitivity ≤ Decision Tree Complexity for all Boolean functions `f`. -/
theorem sensitivityLeDecisionTreeComplexity {t : DecisionTree n} {f : BoolFn n}
    (h_comp : t.computes f) : sensitivity f ≤ t.depth := by
    -- 1. Definition of sensitivity is a Sup (max) over all inputs x.
    unfold sensitivity
    -- 2. To bound a Sup, we show every element is bounded.
    apply Finset.sup_le
    -- 3. Introduce arbitrary x.
    intro x _
    -- 4. Apply Lemmas A and B (sensitivityAt ≤ pathLength ≤ depth).
    calc sensitivityAt f x
    _ ≤ pathLength t x := sensitivityAt_le_pathLength h_comp x
    _ ≤ t.depth        := pathLength_le_depth t x

end DecisionTreeVsSensitivity



/- ----------------------- Bonus Statements to Prove ------------------------ -/
section Bonus

variable {n : ℕ}

theorem DecisionTreeTrivialUpperBound (f : BoolFn n) :
  DecisionTreeComplexity f ≤ n := by
  -- Build the trivial decision tree that queries all variables.
  -- And show that it computes `f`.
  sorry

theorem SensitivityTrivialUpperBound (f : BoolFn n) :
  sensitivity f ≤ n := by
  -- Just use that cardinality of { i | f i ≠ f (flipBit x i)} ≤ n.
  sorry

theorem sensitivityLeDecisionTreeComplexity_V2 (f : BoolFn n) :
  sensitivity f ≤ DecisionTreeComplexity f := by
  -- This runs into a challenge that on needs to show that the set
  -- { d | ∃ t : DecisionTree n, t.computes f ∧ t.depth = d } is non-empty.
  -- The ideas in proof of `DecisionTreeTrivialUpperBound` above might be
  -- applicable here.
  sorry

theorem sensitivityAnd : n = sensitivity (@AND n) := by
  sorry

theorem DecisionTreeComplexityAnd : DecisionTreeComplexity (@AND n) = n := by
  apply Nat.eq_iff_le_and_ge.mpr
  constructor
  · exact DecisionTreeTrivialUpperBound (@AND n)
  · calc
      n = sensitivity (@AND n) := sensitivityAnd
      _ ≤ DecisionTreeComplexity (@AND n) := sensitivityLeDecisionTreeComplexity_V2 (@AND n)

end Bonus
