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
  | DecisionTree.leaf val => sorry
  | DecisionTree.node i left right => sorry
  -- if x i = true, evaluate right branch, else evaluate left branch.

/-- DecisionTree computes a function

A tree computes `f` if its evaluates to `f(x)` for all inputs `x`.
-/
def computes (t : DecisionTree n) (f : BoolFn n) : Prop :=
  sorry

/-- Depth of a DecisionTree

The number of queries made on the worst-case input.
This corresponds to the depth of the tree (0 for leaves).
-/
def depth (t : DecisionTree n) : ℕ := sorry

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

-- Uncomment the following to check outputs:
-- #eval AND2.eval ![false, false]   -- false
-- #eval AND2.eval ![false, true]    -- false
-- #eval AND2.eval ![true, true]     -- true

/-- Decision Tree for 2-bit Parity. -/
def PARITY2 : DecisionTree 2 :=
  .node 0
  (.node 1 (.leaf false) (.leaf true))
  (.node 1 (.leaf true) (.leaf false))

-- Uncomment the following to check outputs:
-- #eval PARITY2.eval ![false, false]    -- false
-- #eval PARITY2.eval ![false, true]     -- true
-- #eval PARITY2.eval ![true, true]      -- false

/- ------------------------------ Sensitivity ------------------------------- -/
section Sensitivity

variable {n : ℕ}

/-- Flips the i-th bit of input x. -/
def flipBit (x : BoolInput n) (i : Fin n) : BoolInput n :=
  sorry

/-- The sensitivity of f at input x: number of neighbors with different function values. -/
def sensitivityAt (f : BoolFn n) (x : BoolInput n) : ℕ :=
  (Finset.univ.filter (fun i => f x ≠ f (flipBit x i))).card

/-- The sensitivity of Boolean function f. -/
def sensitivity (f : BoolFn n) : ℕ :=
  Finset.univ.sup (fun x => sensitivityAt f x)
  -- Note: This is equivalent to the following:
  -- Finset.sup Finset.univ (fun x => sensitivityAt f x)

end Sensitivity

-- Uncomment the following to check outputs:
-- #eval sensitivityAt AND2.eval ![false, false]      -- 0
-- #eval sensitivityAt AND2.eval ![false, true]       -- 1
-- #eval sensitivityAt AND2.eval ![true, true]        -- 2
-- #eval sensitivity AND2.eval                        -- 2
-- #eval sensitivityAt PARITY2.eval ![false, false]   -- 2

/- ----------------- Sensitivity ≤ Decision Tree Complexity ---------------- -/
section DecisionTreeVsSensitivity

variable {n : ℕ}

/-- The length of the path traced by decision tree `t` on input `x`. -/
def pathLength (t : DecisionTree n) (x : BoolInput n) : ℕ :=
  sorry

/-- Lemma A: The path length is always bounded by the tree depth. -/
lemma pathLength_le_depth (t : DecisionTree n) (x : BoolInput n) :
  pathLength t x ≤ t.depth := by
  sorry

/-- Lemma B: Key Lemma.
    If t computes f, the sensitivity at specific input x is bounded by the path length. -/
lemma sensitivityAt_le_pathLength {t : DecisionTree n} {f : BoolFn n}
  (h_comp : t.computes f) (x : BoolInput n) :
  sensitivityAt f x ≤ pathLength t x := by
  induction t generalizing f with
  | leaf val => sorry
  | node i l r ih_l ih_r =>
    unfold pathLength
    by_cases hxi : x i = true
    · -- Case: Go Right
      sorry
    · -- Case: Go Left (Symmetric to above)
      let hxi_false := Bool.eq_false_of_not_eq_true hxi
      sorry

/-- Sensitivity ≤ Decision Tree Complexity for all Boolean functions `f`. -/
theorem sensitivityLeDecisionTreeComplexity {t : DecisionTree n} {f : BoolFn n}
   (h_comp : t.computes f) : sensitivity f ≤ t.depth := by
   -- 1. Unfold definition of sensitivity (it is a Sup).
   -- 2. Apply Finset.sup_le (to bound the max).
   -- 3. Introduce arbitrary x.
   -- 4. Use Lemmas A and B (sensitivityAt ≤ pathLength ≤ depth): use `calc`.
   sorry

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
  -- apply Nat.eq_iff_le_and_ge.mpr to get the goal as AND of ≤ and ≥.
  -- Use `constructor` to show both directions.
  sorry

end Bonus
