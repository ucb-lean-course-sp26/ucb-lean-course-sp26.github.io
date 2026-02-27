/-
  CS 294-268 (Spring 2026)
  Homework 2: Structured Proofs & DFA Correctness - SOLUTIONS

  This file contains complete solutions to all problems in PSet2.lean.
-/

import Mathlib.Tactic

-- =================================================================
-- PART 1: ESSENTIAL LOGIC WARMUP
-- =================================================================

/-
  Task 1: And commutativity.
-/
theorem my_and_comm (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro ⟨hP, hQ⟩
    exact ⟨hQ, hP⟩
  · intro ⟨hQ, hP⟩
    exact ⟨hP, hQ⟩

/-
  Task 2: Existential introduction.
-/
theorem exists_five : ∃ n : Nat, n = 5 := by
  exists 5

/-
  Task 3: Universal quantifier exercise.
-/
theorem forall_elim {α : Type} (P : α → Prop) (y : α) :
  (∀ x, P x) → P y := by
  intro h
  apply h

/-
  Task 4: Uniqueness of zero.
-/
theorem my_unique_zero : ∃! n : Nat, n = 0 := by
  refine ⟨0, rfl, ?_⟩
  intro y hy
  exact hy

/-
  Task 5: Case analysis with decidable.
-/
theorem nat_eq_zero_or_not (n : Nat) : n = 0 ∨ n ≠ 0 := by
  by_cases h : n = 0
  · left
    exact h
  · right
    exact h

-- =================================================================
-- PART 2: DETERMINISTIC FINITE AUTOMATA (DFA) - DEFINITIONS
-- =================================================================

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

abbrev Language (α : Type) := Set (List α)

def DFA.language {α : Type} (M : DFA α) : Language α :=
  { w | accepts M w = true }

theorem mem_language_iff {α : Type} (M : DFA α) (w : List α) :
  w ∈ M.language ↔ accepts M w = true :=
  Iff.rfl

inductive Bit where
  | O | I
deriving Repr, DecidableEq

open Bit

-- =================================================================
-- PART 3: THE endsWithI DFA
-- =================================================================

def endsWithI : DFA Bit :=
{ State  := Bool
, start  := false
, step   := fun _ b =>
    match b with
    | O => false
    | I => true
, accept := fun st => st
}

-- =================================================================
-- PART 4: HELPER LEMMAS ABOUT run
-- =================================================================

/-
  Task 6: run on empty word.
-/
theorem run_nil {α : Type} (M : DFA α) (q : M.State) :
  run M q [] = q := by
  rfl

/-
  Task 7: run on singleton.
-/
theorem run_singleton {α : Type} (M : DFA α) (q : M.State) (a : α) :
  run M q [a] = M.step q a := by
  simp [run]

/-
  Task 8: run is compositional.
-/
theorem run_append {α : Type} (M : DFA α) (q : M.State) (w₁ w₂ : List α) :
  run M q (w₁ ++ w₂) = run M (run M q w₁) w₂ := by
  induction w₁ generalizing q with
  | nil =>
    simp [run]
  | cons a w₁ ih =>
    simp [run]
    exact ih (M.step q a)

-- =================================================================
-- PART 5: PROVING endsWithI CORRECTNESS - STEP FUNCTION
-- =================================================================

/-
  Task 9: endsWithI step function on O.
-/
theorem endsWithI_step_O (st : Bool) :
  endsWithI.step st O = false := by
  rfl

/-
  Task 10: endsWithI step function on I.
-/
theorem endsWithI_step_I (st : Bool) :
  endsWithI.step st I = true := by
  rfl

-- =================================================================
-- PART 6: PROVING endsWithI CORRECTNESS - RUN BEHAVIOR
-- =================================================================

/-
  Task 11: Running endsWithI from false on [O].
-/
theorem endsWithI_run_false_O :
  run endsWithI false [O] = false := by
  simp [run, endsWithI]

/-
  Task 12: Running endsWithI from false on [I].
-/
theorem endsWithI_run_false_I :
  run endsWithI false [I] = true := by
  simp [run, endsWithI]

/-
  Task 13: Running endsWithI on any word ending with I.
-/
theorem endsWithI_run_ends_with_I (w : List Bit) :
  run endsWithI false (w ++ [I]) = true := by
  simp [run_append, run, endsWithI]

/-
  Task 14: Running endsWithI on any word ending with O.
-/
theorem endsWithI_run_ends_with_O (w : List Bit) :
  run endsWithI false (w ++ [O]) = false := by
  simp [run_append, run, endsWithI]

-- =================================================================
-- PART 7: LANGUAGES AND CORRECTNESS
-- =================================================================

def endsWithIWord : List Bit → Prop
  | [] => False
  | [O] => False
  | [I] => True
  | _ :: w' => endsWithIWord w'

def endsWithI_lang : Language Bit :=
  { w | endsWithIWord w }

/-
  Task 15: Membership in endsWithI_lang.
-/
theorem I_in_endsWithI_lang : [I] ∈ endsWithI_lang := by
  simp [endsWithI_lang, endsWithIWord]

/-
  Task 16: Non-membership in endsWithI_lang.
-/
theorem O_not_in_endsWithI_lang : [O] ∉ endsWithI_lang := by
  simp [endsWithI_lang, endsWithIWord]

/-
  Task 17: endsWithI accepts [I].
-/
theorem endsWithI_accepts_I :
  accepts endsWithI [I] = true := by
  simp [accepts, run, endsWithI]

/-
  Task 18: endsWithI rejects [O].
-/
theorem endsWithI_rejects_O :
  accepts endsWithI [O] = false := by
  simp [accepts, run, endsWithI]

/-
  Task 19: endsWithI rejects empty word.
-/
theorem endsWithI_rejects_empty :
  accepts endsWithI [] = false := by
  simp [accepts, run, endsWithI]

/-
  Task 20: endsWithI accepts words ending with I.
-/
theorem endsWithI_accepts_suffix_I (w : List Bit) :
  accepts endsWithI (w ++ [I]) = true := by
  -- 1. Unfold 'accepts' definition, but keep 'endsWithI' as a constant
  rw [accepts]
  -- 2. Force reduction of 'endsWithI.start' to 'false' to match our helper lemma
  have h_start : endsWithI.start = false := rfl
  rw [h_start]
  -- 3. Now the term matches 'run endsWithI false ...' exactly
  rw [endsWithI_run_ends_with_I]
  -- 4. Finally, reduce 'endsWithI.accept true' to 'true'
  rfl

/-
  Task 21: endsWithI rejects words ending with O.
-/
theorem endsWithI_accepts_suffix_O (w : List Bit) :
  accepts endsWithI (w ++ [O]) = false := by
  rw [accepts]
  have h_start : endsWithI.start = false := rfl
  rw [h_start]
  rw [endsWithI_run_ends_with_O]
  rfl

/-
  Task 22: Language equality for endsWithI.
-/
theorem endsWithI_language_correct :
  endsWithI.language = endsWithI_lang := by
  ext w
  simp [DFA.language, endsWithI_lang, accepts]
  induction w with
  | nil =>
    simp [endsWithIWord, endsWithI, run]
  | cons a w ih =>
    cases a
    · -- Case: current bit is O
      simp [endsWithI, run]
      cases w with
      | nil => simp [endsWithIWord, run]
      | cons b w' =>
        simp [endsWithIWord]
        -- Logic: run endsWithI false (O :: b :: w') = run endsWithI false (b :: w')
        simp [run]
        exact ih
    · -- Case: current bit is I
      simp [endsWithI, run]
      cases w with
      | nil => simp [endsWithIWord, run]
      | cons b w' =>
      -- ... inside the | cons a w ih => ... | cons b w' => block ...

        -- 1. Simplify the RHS: endsWithIWord (I :: b :: w') -> endsWithIWord (b :: w')
        simp [endsWithIWord]

        -- 2. Bring in the Inductive Hypothesis.
        --    IH says: accepts endsWithI (b :: w') ↔ endsWithIWord (b :: w')
        rw [←ih]

        -- 3. Unfold 'endsWithI' so the IH term matches the goal structure
        simp [endsWithI]
        simp [run]


-- =================================================================
-- PART 8: THE evenIs DFA
-- =================================================================

def evenIs : DFA Bit :=
{ State  := Bool
, start  := false
, step   := fun st b =>
    match b with
    | O => st
    | I => !st
, accept := fun st => !st
}

-- =================================================================
-- PART 9: PROVING evenIs CORRECTNESS
-- =================================================================

/-
  Task 20: evenIs step on O preserves state.
-/
theorem evenIs_step_O (st : Bool) :
  evenIs.step st O = st := by
  rfl

/-
  Task 21: evenIs step on I flips state.
-/
theorem evenIs_step_I (st : Bool) :
  evenIs.step st I = !st := by
  rfl

def countI : List Bit → Nat
  | [] => 0
  | O :: w => countI w
  | I :: w => 1 + countI w

def evenI_lang : Language Bit :=
  { w | Even (countI w) }

/-
  Task 23: Membership in evenI_lang.
-/
theorem empty_in_evenI_lang : [] ∈ evenI_lang := by
  simp [evenI_lang, countI]

/-
  Task 24: Membership in evenI_lang.
-/
theorem II_in_evenI_lang : [I, I] ∈ evenI_lang := by
  simp [evenI_lang, countI]

/-
  Task 25: Non-membership in evenI_lang.
-/
theorem I_not_in_evenI_lang : [I] ∉ evenI_lang := by
  simp [evenI_lang, countI]

/-
  Task 26: evenIs accepts empty word.
-/
theorem evenIs_accepts_empty :
  accepts evenIs [] = true := by
  simp [accepts, run, evenIs]

/-
  Task 27: evenIs accepts [I, I].
-/
theorem evenIs_accepts_II :
  accepts evenIs [I, I] = true := by
  simp [accepts, run, evenIs]

/-
  Task 28: evenIs rejects [I].
-/
theorem evenIs_rejects_I :
  accepts evenIs [I] = false := by
  simp [accepts, run, evenIs]

/-
  Task 29: Reading two I's returns to the same state.
-/
theorem evenIs_two_I_same_state (st : Bool) :
  run evenIs st [I, I] = st := by
  cases st <;> simp [run, evenIs]

/-
  Task 30: Language equality for evenIs.
-/
theorem evenIs_language_correct :
  evenIs.language = evenI_lang := by
  ext w
  simp [DFA.language, evenI_lang, accepts]
  -- We prove a stronger lemma generalizing the start state
  have h_gen : ∀ st, (evenIs.accept (run evenIs st w)) = (if Even (countI w) then !st else st) := by
    induction w with
    | nil =>
      intro st
      simp [run, countI, evenIs]
    | cons a w ih =>
      intro st
      cases a
      · -- Case: a = O
        -- 1. Simplify 'run' (step O returns st) and 'countI' (O adds nothing)
        specialize ih (evenIs.step st O)
        -- 1. Rewrite O :: w as [O] ++ w so we can use run_append
        rw [←List.singleton_append]

        -- 2. Split the run using run_append
        --    run ... ([O] ++ w) becomes run ... (run ... [O]) w
        rw [run_append]

        -- 3. Evaluate the single step using run_singleton
        --    run ... [O] becomes step ... O
        rw [run_singleton]
        rw[ih]

        -- 4. Simplify the specific step for 'O' (it returns st)
        --    and simplify countI (O adds nothing)
        simp [evenIs, countI]

      · -- Case: a = I
        specialize ih (evenIs.step st I)
        rw [←List.singleton_append]
        rw [run_append]
        rw [run_singleton]
        rw[ih]
        simp [evenIs, countI]
        -- 1. Simplify the parity logic: Even (1 + n) becomes ¬Even n
        simp [Nat.add_comm, Nat.even_add_one]
        simp [←Nat.not_even_iff_odd]

  -- Apply lemma to start state (false)
  specialize h_gen evenIs.start
  rw [h_gen]
  simp [evenIs]

-- =================================================================
-- END OF HOMEWORK 2 SOLUTIONS
-- =================================================================
