------- Transient Commands -------

#check 5           -- ℕ
#eval 5            -- 5

#check "Hello"     -- String

#check [1, 2, 3]   -- List Nat

/-- Number of apples in basket

This docstring shows up when hovering over `numApples`.
-/
def numApples : Nat := 5

#check numApples
#eval numApples
#print numApples

#check Nat      -- Type
#check Type     -- Type 1
#check Type 1   -- Type 2

#check List Nat
#check List


------- Binders: Explicit, Implicit & Instance -------

def f (x : Nat) (y : Nat) : Nat := x * y

theorem inEq (a b c : Nat) (h : b < c) : a + b < a + c := by
  exact Nat.add_lt_add_left h a

#check f
#eval f 2 3  -- 6

def g (α : Type) (a : α) : α := a

#eval g Nat 5

def g' {α : Type} (a : α) : α := a

#eval g' 5


-- def genericAdd {α : Type} (a b : α) : α := a + b  -- ERROR!
def genericAdd {α : Type} [Add α] (a b : α) : α := a + b

------- `structure` types ("Product") -------

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

------- `inductive` types ("Sum") -------

/-- An enumerative type for days of the week. -/
inductive Day where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday

#check Day.sunday   -- Day.sunday : Day

namespace Day
  /-- Next day of the week. -/
  def nextDay (day : Day) : Day :=
    match day with
    | sunday => monday
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => saturday
    | saturday => sunday
end Day

#eval Day.sunday.nextDay   -- Day.monday

/-- An inductive type for Natural numbers. -/

inductive Natural where
  | zero
  | succ : Natural → Natural

#check Natural.succ Natural.zero = Natural.zero.succ

/-- An inductive type for {0, 1}^*. -/
inductive BinStr where
  | eps
  | zero: BinStr → BinStr
  | one: BinStr -> BinStr

#check BinStr.eps
#check BinStr.eps.zero
#check BinStr.eps.zero.one

------- Some Examples in Theorem Formalization -------

theorem simple_math : 2 + 5 = 7 := by
  rfl -- "Reflexivity" (by definition, they are equal)


/-- Fermat's Last Theorem. -/
theorem fermatsLastTheorem
  (n a b c : Nat) (hn : n > 2) (ha : a > 0) (hb : b > 0) (hc : c > 0)
:
  a^n + b^n ≠ c^n
:= by
  sorry  -- Proof is to be filled!


/--
  sumFirstN(n) = sum_{k=0}^n k
-/
def sumFirstN (n : Nat) :=
  match n with
  | 0 => 0
  | k + 1 => sumFirstN k + k + 1

/--
 sumSeq(f, n) = sum_{k=0}^n f(k)
-/
def sumSeq {α : Type} [Add α] (f : Nat → α) (n : Nat) :=
  match n with
  | 0 => f 0
  | d + 1 => sumSeq f d + f (d + 1)

/-- Returns square of the input `x`.-/
def square {α : Type} [Mul α] (x : α) := x * x

#eval sumSeq square 3  -- 14 (= 1 + 4 + 9)

/-- sum_{k=0}^n k = n * (n + 1) * (2 * n + 1) / 6. -/
theorem sum_of_squares (n : Nat) :
  6 * sumSeq square n = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ d hd =>
    simp [sumSeq, square]
    ring_nf
    linarith


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

------- Simple Tactics: rfl -------
example : 2 + 2 = 4 := by
  rfl

example (a : Nat) : a = a := by
  rfl

------- Simple Tactics: intro -------
example (p q : Prop) : p → q → p := by
  intro h_p h_q
  exact h_p


------- Simple Tactics: exact -------
example (p : Prop) (h : p) : p := by
  exact h


------- Simple Tactics: apply -------
example (p q : Prop)
        (h_imp : p → q) (h_p : p) : q := by
  apply h_imp
  exact h_p


------- Simple Tactics: rw -------
example (a b c : Nat)
        (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]
  exact h2


------- Simple Tactics: simp -------
example (x : Nat) : x + 0 = x := by
  simp    -- try `simp?`

example (p : Prop) : p ∧ True ↔ p := by
  simp    -- try `simp?`


------- Simple Tactics: cases -------
example (n : Nat) : n = 0 ∨ n ≠ 0 := by
  cases n with
  | zero =>
      left --we will get to this in Lecture 3
      rfl
  | succ k =>
      right --we will get to this in Lecture 3
      intro h
      cases h


------- Simple Tactics: have -------
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  have hq : q := by
    apply hpq
    exact hp
  exact hq


------- Simple Tactics: induction -------
example (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.add_succ, ih]


------- Simple Tactics: constructor -------
example (p q : Prop)
        (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq
  /- the symbol · is syntax for "fill in the current subgoal"
  it makes goal structure explicit, the proof will not be affected if removed. -/
