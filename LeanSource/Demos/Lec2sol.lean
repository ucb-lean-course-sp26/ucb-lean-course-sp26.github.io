/- Lecture 2 -/

import Mathlib.Tactic

---------------- Term vs Tactic Mode ----------------

/-- Example showing "Modus Ponens" in "Term mode". -/
theorem mp1 (p q : Prop) (f : p → q) (hp : p) : q := f hp

/-- Example showing "Modus Ponens" in "Tactic mode". -/
theorem mp1' (p q : Prop) (f : p → q) (hp : p) : q := by
  -- Tactic state seeks a term of type `q`.
  apply f
  -- Tactic state seeks a term of type `p`.
  exact hp

#print mp1
#print mp1'  -- This is same as `mp1`.

/-- Another example similar to "Modus Ponens" in "Term mode". -/
theorem mp2 (p q r : Prop) (f : p → q → r) (hp : p) (hq : q) : r := f hp hq

/-- Another example similar to "Modus Ponens" in "Tactic mode". -/
theorem mp2' (p q r : Prop) (f : p → q → r) (hp : p) (hq : q) : r := by
  -- Tactic state seeks a term of type `r`
  apply f
  -- Tactic state has two goals, one seeks term of type `p`, other of type `q`.
  exact hp
  exact hq

#print mp2
#print mp2'  -- This is the same as `mp2`.

/- Tactic Mode can also be applied for definitions. -/
def addInTermMode (x y : Nat) : Nat := Nat.add x y  -- equivalently, x + y

def addInTacticMode (x y : Nat) : Nat := by
  apply Nat.add
  exact x
  exact y

#print addInTermMode
#print addInTacticMode  -- This is same as `addInTermMode`.
#eval addInTacticMode 2 3  -- Output: 5

---------- Clarifications regarding `#check`, `#eval`, `#print` ----------

/-
#check : "What is its type?"
         Can be applied on any term `t` to display its type.

#eval  : "What is its value?"
         Can be applied on terms that are computable. Cannot run on a theorem
         or non-computable expressions, such as those involving real numbers.

#print : "How is it defined?"
         Can be applied on any "name", but not expressions.
-/

#check 5
#check List
#check Or
#check 1 + 1
#check Bool

#eval 2 + 3
#eval false ∨ true
-- #eval mp1   -- Throws an error; cannot eval a "theorem"

#print Nat
#print Or
-- #print 2 + 3   -- Throws an error; cannot print an expression.

---------------------- Recap of tactics from last time ----------------------
/-
We will recap tactics covered last time through some exercises:
`exact`, `intro`, `rfl`, `apply`, `rw`, `constructor`, `have`

Let's walk through some examples!

Acknowledgement: Course by Yuvul Filmus
https://yuvalfilmus.cs.technion.ac.il/courses/?crid=1777

Solutions: https://github.com/YuvalFilmus/Exercises/blob/main/Exercises/SolutionWeek1.lean
-/

lemma imp_1 (A B : Prop) : A → (B → A) := by
  intro hA _hB
  exact hA

lemma imp_2 (A B : Prop) : A → (A → B) → B := by
  intro hA hAB
  exact hAB hA

lemma imp_3 (A B C : Prop) : (A → (B → C)) → ((A → B) → (A → C)) := by
  intro hABC hAB hA
  exact hABC hA (hAB hA)

lemma proving_iff (A : Prop) : A ↔ A := by
  constructor
  · intro h; exact h
  · intro h; exact h

lemma using_iff (A B : Prop) : (A ↔ B) → B → A := by
  intro hAB hB
  exact hAB.mpr hB

lemma proving_or (A B : Prop) : A → A ∨ B := by
  intro hA
  left
  exact hA

lemma using_or (A B : Prop) : A ∨ B → B ∨ A := by
  intro h
  cases h with
  | inl hA => right; exact hA
  | inr hB => left; exact hB

lemma proving_and (A B : Prop) : A → (A → B) → A ∧ B := by
  intro hA hAB
  constructor
  · exact hA
  · exact hAB hA

lemma using_and (A B : Prop) : A ∧ B → A ∨ B := by
  intro h
  left
  exact h.1

lemma complex (A B : Prop) : A ∨ (A ∧ B) ↔ A := by
  constructor
  · intro h
    cases h with
    | inl hA => exact hA
    | inr hAB => exact hAB.1
  · intro hA
    left
    exact hA

lemma proving_negation_1 (A B : Prop) : ¬ A → ¬ (A ∧ B) := by
  intro hnotA hAB
  exact hnotA hAB.1

lemma proving_negation_2(A B : Prop) : (A → B) → (¬ B → ¬ A) := by
  intro hAB hnotB hA
  exact hnotB (hAB hA)

-------------- Tactics for linear / polynomial expressions --------------
/-
Additional tactics:
`omega`: Presburger arithmetic, e.g. linear constraints over ℕ.
`linarith`: Handles equality, inequality goals over fields/rings (e.g. ℝ ℚ)
`ring` : Proves polynomial identities (=)
-/

theorem omega_ex (n : ℕ) : (n - 5) + 5 ≥ n := by
  omega

theorem linarith_ex (x y : ℚ) (h1 : 2 * x < y) (h2 : y < 10) : x < 5 := by
  linarith

theorem ring_ex (a b : ℤ) : (a + b) * (a - b) = a^2 - b^2 := by
  ring

---------------------- The `calc` tactic ----------------------

/- A `calc` block improves readability. -/
example (a b c d : Nat) (h1 : a ≤ b) (h2 : b = c) (h3 : c < d) : a < d :=
  calc
    a ≤ b := h1
    _ = c := h2
    _ < d := h3

/- How this could be done without `calc` tactic. -/
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : b = c) (h3 : c < d) : a < d := by
  -- We want to prove a < d. We can break this into a ≤ c and c < d.
  apply lt_of_le_of_lt
  · -- Subgoal 1: prove a ≤ c
    apply le_of_le_of_eq
    · exact h1 -- a ≤ b
    · exact h2 -- b = c
  · exact h3   -- c < d

/- Or in pure "term mode". -/
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : b = c) (h3 : c < d) : a < d :=
  lt_of_le_of_lt (le_of_le_of_eq h1 h2) h3


/- `calc` works for other operations as well, e.g. "divides". -/
example (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  calc
    a ∣ b := h1
    _ ∣ c := h2

/-
Acknowledgement: "The Mechanics of Proof" by Heather Macbeth
https://hrmacbeth.github.io/math2001/index.html
-/

example {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) : (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by ring


-- Now, let's try to do this exercise!
example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
    r = r + 2 * s - 2 * s := by ring
    _ = -1 - 2 * s := by rw [h2]
    _ = -1 - 2 * 3 := by rw [h1]
    _ = -7 := by ring

---------------------- More on `inductive` types ----------------------

/-- Day of the week. -/
inductive Day where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday

-- Examples demonstrating `match`.

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

-- Examples demonstrating `cases`.

/-- Previous of the next day is the same day. -/
theorem nextPreviousIsToday (d : Day) : d.next.previous = d := by
  cases d   -- Now there are 7 subgoals.
  rfl
  rfl
  rfl
  rfl
  rfl
  rfl
  rfl

theorem nextPreviousIsToday' (d : Day) : d.next.previous = d := by
  cases d <;> rfl  -- Apply the same tactic for all sub-goals.

-- `cases` destructs `empty` types.
example : Day.sunday ≠ Day.monday := by
  intro h    -- h : Day.sunday = Day.monday ⊢ False
  cases h    -- h is already false by "disjoint constructors".

-- By default `inductive` classes are not computable.
-- Uncomment the following to see an error.
-- #eval Day.sunday = Day.monday
-- To make this work, add `deriving DecidableEq` to definition of `Day`.

/- Proof by `induction` for a Binary Tree. -/
inductive BinTree where
  | empty : BinTree
  | node (val : Nat) (left : BinTree) (right : BinTree) : BinTree


def mirror (t : BinTree) : BinTree :=
  match t with
  | .empty => .empty
  | .node n l r => .node n (mirror r) (mirror l)
-- Note: "." was required above because we are not inside `BinTree` namespace.

/- Example binary tree:
    2
   / \
  1   6
     / \
    5   9
-/
def binTree1 : BinTree :=
  .node
  2
  (.node
      1
      .empty
      .empty
  )
  (.node
      6
      (.node
          5
          .empty
          .empty
      )
      (.node
          9
          .empty
          .empty
      )
  )

#eval mirror binTree1

/-- Taking the mirror operation twice returns the same binary tree. -/
theorem mirror_mirror (t : BinTree) : mirror (mirror t) = t := by
  induction t with
  | empty =>
    rfl
  | node n l r ih_l ih_r =>
    -- n : Nat  (Value)
    -- l : Tree (Left branch)
    -- r : Tree (Right branch)
    -- ih_l : inductive hypothesis for l
    -- ih_r : inductive hypothesis for r
    dsimp [mirror]
    rw [ih_l, ih_r]
