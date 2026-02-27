/-
In this file, we introduce the basics of error-correcting codes and formalize
several fundamental results in coding theory.

Topics covered:
  1. Basic definitions: alphabets, codewords, codes, Hamming distance
  2. Example codes: repetition code, parity code
  3. Error detection and correction capability
  4. The Hamming bound (sphere-packing bound)
  5. The Singleton bound

This file can serve as a starting point for formalizing more advanced results
in coding theory. For an introduction to the subject, see:

Reference: "A First Course in Coding Theory" by Raymond Hill
Reference: "The Theory of Error-Correcting Codes" by MacWilliams and Sloane
-/

import Mathlib
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.InformationTheory.Hamming

/-! ─────────────────────────────────────────────────────────────────────────
## Part 1: Basic Definitions
──────────────────────────────────────────────────────────────────────────── -/

/-!
We work over an **alphabet** `α` — a finite type representing the symbols we
can use. Common choices:

* `Bool` — binary alphabet `{0, 1}`
* `Fin q` — q-ary alphabet `{0, 1, …, q-1}`
* `ZMod p` — integers modulo a prime p (a field)

A **codeword** of length n is a function `Fin n → α`.
A **code** is a set (here a `Finset`) of codewords.
-/

section Definitions

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {n : ℕ}

/-- A codeword of length n over alphabet α is just a function Fin n → α. -/
abbrev Codeword (n : ℕ) (α : Type*) := Fin n → α

/-- A code of length n over α is a finite set of codewords. -/
abbrev Code (n : ℕ) (α : Type*) := Finset (Codeword n α)

/-!
### Hamming Distance

The **Hamming distance** between two codewords is the number of positions
in which they differ. For example:

    u = 0 1 1 0 1
    v = 0 0 1 1 1
          ^   ^      ← 2 positions differ

So d(u, v) = 2.

Mathlib already provides `hammingDist` in `Mathlib.InformationTheory.Hamming`.
We give a more transparent definition here for pedagogical purposes.
-/

/-- Hamming distance: the number of positions where two codewords differ. -/
def hammingDist' (u v : Codeword n α) : ℕ :=
  (Finset.univ.filter (fun i => u i ≠ v i)).card

-- Let's evaluate on a small example to see Hamming distance in action.
#eval hammingDist (![true, false, true, false, true] : Fin 5 → Bool)
                  ![true, true,  true, true,  true]
-- Expected: 2 (positions 1 and 3 differ)

/-- Hamming weight: the number of nonzero positions (distance from all-zeros). -/
def hammingWeight [Zero α] (u : Codeword n α) : ℕ :=
  (Finset.univ.filter (fun i => u i ≠ 0)).card

/-!
### Minimum Distance

The **minimum distance** of a code C (with at least 2 codewords) is:

    d(C) = min { d(u, v) | u, v ∈ C, u ≠ v }

This is the most important parameter of a code for error-correction purposes.
-/

/-- A code C has minimum distance d if d is the minimum Hamming distance
    between any two distinct codewords. -/
def hasMinDist (C : Code n α) (d : ℕ) : Prop :=
  sorry

-- def hasMinDist (C : Code n α) (d : ℕ) : Prop :=
--   (∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d) ∧
--   (∀ u ∈ C, ∀ v ∈ C, u ≠ v → hammingDist u v ≥ d)

end Definitions

/-! ─────────────────────────────────────────────────────────────────────────
## Part 2: Example Codes
──────────────────────────────────────────────────────────────────────────── -/

section ExampleCodes

/-!
### The Repetition Code

The simplest code: to send a single bit, repeat it n times.
For n = 3 (the triple repetition code):
    0 → 000
    1 → 111

This is a (3, 2, 3)-code: length 3, two codewords, minimum distance 3.
-/

-- The binary repetition code of length n.
-- def repetitionCode (n : ℕ) : Code n Bool :=
--   sorry

def repetitionCode (n : ℕ) : Code n Bool :=
  {(fun _ => false), (fun _ => true)}

-- Check the size: the repetition code has exactly 2 codewords (for n ≥ 1).
example (n : ℕ) (hn : n ≥ 1) : (repetitionCode n).card = 2 := by
  simp only [repetitionCode]
  rw [Finset.card_pair]
  intro h_eq
  have := congr_fun h_eq ⟨0, by omega⟩
  simp at this

-- The repetition code of length 3 has minimum distance 3.
#eval hammingDist ((fun (_ : Fin 3) => false)) (fun _ => true)
-- Expected: 3

/-!
### The Parity Check Code

Add a parity bit to detect single errors. A binary word x₁ x₂ … xₙ is in
the parity code iff it has an even number of 1s, i.e.,
x₁ + x₂ + … + xₙ ≡ 0 (mod 2).
-/

-- The binary parity code of length n: all words with even Hamming weight.
def parityCode (n : ℕ) : Code n Bool :=
  Finset.univ.filter (fun (c : Fin n → Bool) =>
    (Finset.univ.filter (fun i => c i = true)).card % 2 = 0)

-- The parity code of length 7 is a [7, 6, 2]-code (detects single errors).
-- It has 2^6 = 64 codewords (all 7-bit words with even weight).
#eval (parityCode 7).card  -- Expected: 64

/-!
### The [7, 4, 3] Hamming Code

The Hamming code Ham(3, 2) is a [7, 4, 3] perfect binary code:
  - length 7, dimension 4 (16 codewords), minimum distance 3.

A binary word x = (x₁ … x₇) is a Hamming codeword iff Hx = 0 (mod 2),
where H is the 3×7 parity-check matrix whose columns are all nonzero
binary 3-vectors. Using column order 1..7 (in binary: 001,010,011,100,101,110,111):

    H = [ 0 0 0 1 1 1 1 ]
        [ 0 1 1 0 0 1 1 ]
        [ 1 0 1 0 1 0 1 ]

We represent each bit as a `Bool` (false = 0, true = 1) and XOR as addition
mod 2 via `Bool.xor` (i.e., `bxor`).
-/

-- The [7, 4, 3] Hamming code: all binary words of length 7 satisfying Hx = 0 (mod 2).
-- Using parity-check matrix H with columns = all nonzero binary 3-vectors (in order 1..7):
--   H row 0 (bit 2): columns where (j+1) has bit 2 set → j ∈ {3,4,5,6}
--   H row 1 (bit 1): columns where (j+1) has bit 1 set → j ∈ {1,2,5,6}
--   H row 2 (bit 0): columns where (j+1) has bit 0 set → j ∈ {0,2,4,6}
def hammingCode74 : Code 7 Bool :=
  Finset.univ.filter (fun (x : Fin 7 → Bool) =>
    let s0 := (x 3).xor ((x 4).xor ((x 5).xor (x 6)))   -- H row 0
    let s1 := (x 1).xor ((x 2).xor ((x 5).xor (x 6)))   -- H row 1
    let s2 := (x 0).xor ((x 2).xor ((x 4).xor (x 6)))   -- H row 2
    (!s0) && (!s1) && (!s2))

-- The [7,4,3] code has 16 = 2^4 codewords.
#eval hammingCode74.card   -- Expected: 16

-- Verify the all-zeros word is a codeword.
#eval decide ((fun _ => false) ∈ hammingCode74)   -- Expected: true

-- Verify a known Hamming codeword: x = [1,1,0,1,0,0,1] (0-indexed)
-- s0 = x3⊕x4⊕x5⊕x6 = 1⊕0⊕0⊕1 = 0 ✓
-- s1 = x1⊕x2⊕x5⊕x6 = 1⊕0⊕0⊕1 = 0 ✓
-- s2 = x0⊕x2⊕x4⊕x6 = 1⊕0⊕0⊕1 = 0 ✓
#eval decide (![true, true, false, true, false, false, true] ∈ hammingCode74)  -- Expected: true

end ExampleCodes

/-! ─────────────────────────────────────────────────────────────────────────
## Part 3: Error Detection and Correction
──────────────────────────────────────────────────────────────────────────── -/

section ErrorCorrection

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {n : ℕ}

/-!
### Hamming Balls

The Hamming ball of radius r centered at c consists of all words within
Hamming distance r from c. These are the words that could have been received
if c was sent and at most r errors occurred.
-/

/-- The Hamming ball of radius r centered at u: all words within distance r. -/
def hammingBall (u : Codeword n α) (r : ℕ) : Finset (Codeword n α) :=
  Finset.univ.filter (fun v => hammingDist u v ≤ r)

-- Check: how many binary words are within distance 1 from 000?
#eval (hammingBall (n := 3) (α := Bool) (fun _ => false) 1).card
-- Expected: 4  (000, 001, 010, 100)

/-!
### t-Error Correction via Ball Packing

**Key Lemma:** If a code C has minimum distance d ≥ 2t+1, then the Hamming
balls of radius t around distinct codewords are pairwise disjoint.

**Proof:** Suppose some word w ∈ B(u, t) ∩ B(v, t) for distinct u, v ∈ C.
By the triangle inequality:
    d(u, v) ≤ d(u, w) + d(w, v) ≤ t + t = 2t

But d(u, v) ≥ 2t + 1, contradiction.

**Consequence:** Nearest-neighbor decoding correctly identifies the sent
codeword from any received word with ≤ t errors.
-/

/-- If the minimum distance is ≥ 2t+1, balls of radius t are pairwise disjoint. -/
lemma hammingBalls_disjoint (C : Code n α) (t : ℕ)
    (h_dist : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → 2 * t + 1 ≤ hammingDist u v) :
    ∀ u ∈ C, ∀ v ∈ C, u ≠ v → Disjoint (hammingBall u t) (hammingBall v t) := by
  sorry

/-!
### Error Correction Capability

**Theorem:** A code with minimum distance d can correct up to ⌊(d-1)/2⌋ errors.
Equivalently, if d ≥ 2t+1, the code is t-error-correcting: every received word
within distance t of exactly one codeword, so nearest-neighbor decoding succeeds.

Proof: if c was sent and r was received with d(c, r) ≤ t, then:
  • c is in the ball B(c, t)
  • any other codeword c' satisfies d(c', r) ≥ d(c, c') - d(c, r) ≥ d - t ≥ t+1 > t
    (using the reverse triangle inequality and d ≥ 2t+1)
so c is the unique closest codeword to r.
-/

/-- A code with minimum distance ≥ 2t+1 can correct t errors:
    if c ∈ C is the sent codeword and r is received with d(c, r) ≤ t,
    then no other codeword is within distance t of r. -/
theorem error_correction (C : Code n α) (t : ℕ)
    (h_dist : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → 2 * t + 1 ≤ hammingDist u v)
    (c r : Codeword n α) (hc : c ∈ C)
    (h_errors : hammingDist c r ≤ t) :
    ∀ c' ∈ C, c' ≠ c → hammingDist c' r > t := by
  sorry

/-!
### Nearest-Neighbor Decoding Algorithm

Given a code C and a received (possibly noisy) word r, the nearest-neighbor
decoder finds the codeword in C closest to r in Hamming distance.

The algorithm: for each codeword c ∈ C, compute d(c, r); return the c with
minimum distance. If there is a tie, we return an arbitrary winner (the fold
will return the last minimum found).

This is a brute-force O(|C| · n) algorithm; for large codes, more efficient
syndrome-based decoders are used in practice.
-/

/-- Nearest-neighbor decoder: find the codeword in C closest to r (noncomputable).
    Returns `none` if C is empty, `some c` where c achieves the minimum distance otherwise. -/
noncomputable def decode (C : Code n α) (r : Codeword n α) : Option (Codeword n α) :=
  if h : C.Nonempty then
    some (C.exists_min_image (fun c => hammingDist c r) h).choose
  else none

/-- The decoded codeword (when it exists) is indeed a member of C. -/
theorem decode_mem (C : Code n α) (r : Codeword n α) (c : Codeword n α)
    (h : decode C r = some c) : c ∈ C := by
  simp only [decode] at h
  split_ifs at h with hne
  · -- h : some (choose ...) = some c, so choose ... = c
    have heq : (C.exists_min_image (fun c => hammingDist c r) hne).choose = c :=
      Option.some.inj h
    rw [← heq]
    exact (C.exists_min_image (fun c => hammingDist c r) hne).choose_spec.1

/-- Computable nearest-neighbor decoder for `#eval`.
    Takes an explicit list of codewords and finds the closest to r. -/
def decodeEval {n : ℕ} {α : Type*} [DecidableEq α] [Fintype α]
    (codewords : List (Fin n → α)) (r : Fin n → α) : Option (Fin n → α) :=
  codewords.foldl
    (fun best c =>
      match best with
      | none   => some c
      | some b => if hammingDist c r < hammingDist b r then some c else best)
    none

/-!
### Decoding Examples

We use `decodeEval` (the computable decoder) to test nearest-neighbor decoding
on noisy codewords. We pass the code as an explicit list of codewords.
-/

-- ── Repetition code decoding ──────────────────────────────────────────────

-- The triple repetition code codewords as a list: {000, 111}
def repCode3 : List (Fin 3 → Bool) :=
  [(fun _ => false), (fun _ => true)]

-- Sent: 111, received: 110 (one error at position 2)
-- Expected decode: 111 (closer to 111 than 000)
#eval decodeEval repCode3 ![true, true, false]
-- Expected: some (fun _ => true)  i.e. "111"

-- Sent: 000, received: 010 (one error at position 1)
-- Expected decode: 000
#eval decodeEval repCode3 ![false, true, false]
-- Expected: some (fun _ => false)  i.e. "000"

-- Sent: 000, received: 011 (two errors — beyond correction capability t=1)
-- The decoder still picks the closest, but correctness is not guaranteed.
#eval decodeEval repCode3 ![false, true, true]
-- Returns some (fun _ => true) because d(111, 011) = 1 < d(000, 011) = 2

-- ── [7, 4, 3] Hamming code decoding ──────────────────────────────────────

-- The [7,4,3] code corrects t=1 error (min dist 3 ≥ 2·1+1).

-- Build the codeword list for evaluation.
-- We enumerate all Fin 7 → Bool functions via their bit representation.
def hammingCode74List : List (Fin 7 → Bool) :=
  (List.range 128).filterMap (fun k =>
    let x : Fin 7 → Bool := fun i => (k >>> i.val &&& 1) == 1
    let s0 := (x 3).xor ((x 4).xor ((x 5).xor (x 6)))
    let s1 := (x 1).xor ((x 2).xor ((x 5).xor (x 6)))
    let s2 := (x 0).xor ((x 2).xor ((x 4).xor (x 6)))
    if (!s0) && (!s1) && (!s2) then some x else none)

#eval hammingCode74List.length  -- Expected: 16

-- Sent: 0000000, received: 0000001 (one error at position 6)
-- Expected: decoded back to 0000000
#eval decodeEval hammingCode74List ![false, false, false, false, false, false, true]

-- Sent: 1101001 = ![t,t,f,t,f,f,t], received: 1101011 (flip bit 5)
-- Expected: decoded back to 1101001
#eval decodeEval hammingCode74List ![true, true, false, true, false, true, true]

/-!
### Erasure Correction

An **erasure** is a position whose value is completely lost in transmission
(the receiver knows *which* positions were erased, but not what they were).
This is strictly easier than an error, where the receiver doesn't know which
positions are wrong.

**Key result:** A code with minimum distance d can correct up to d-1 erasures.

**Proof:** Suppose codeword c was sent and positions E ⊆ [n] with |E| ≤ d-1
were erased. We claim c is the unique codeword consistent with the received
word on the unerased positions.

Suppose c' ≠ c is another codeword consistent with the received word.
Then c and c' agree on all unerased positions, so they can only differ on
the erased positions. Therefore d(c, c') ≤ |E| ≤ d-1 < d, contradicting
the minimum distance of the code.

We model an erased codeword as `Fin n → Option α`:
  `some a` means position i was received as symbol a,
  `none`   means position i was erased.
-/

/-- An erased codeword: each position is either received (`some`) or erased (`none`). -/
abbrev ErasedWord (n : ℕ) (α : Type*) := Fin n → Option α

/-- A codeword c is consistent with an erased word e if every unerased position matches. -/
def consistent (c : Codeword n α) (e : ErasedWord n α) : Prop :=
  ∀ i, e i = none ∨ e i = some (c i)

instance {α : Type*} [DecidableEq α] {n : ℕ}
    (c : Codeword n α) (e : ErasedWord n α) : Decidable (consistent c e) :=
  Fintype.decidableForallFintype

/-- The number of erased positions. -/
def numErasures (e : ErasedWord n α) : ℕ :=
  (Finset.univ.filter (fun i => e i = none)).card

/-- A code with minimum distance d can correct up to d-1 erasures:
    if c ∈ C is sent and at most d-1 positions are erased, then c is
    the unique codeword consistent with the erased received word. -/
theorem erasure_correction (C : Code n α) (d : ℕ)
    (h_dist : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → d ≤ hammingDist u v)
    (c : Codeword n α) (hc : c ∈ C)
    (e : ErasedWord n α) (h_cons : consistent c e)
    (h_era : numErasures e ≤ d - 1) :
    ∀ c' ∈ C, consistent c' e → c' = c := by
  intro c' hc' hcons'
  by_contra hne
  -- Any position where c and c' differ must be erased:
  -- if e i = some a then both c and c' match a, so c i = c' i.
  have h_sub : hammingDist c c' ≤ numErasures e := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]    -- hi : c i ≠ c' i; we show e i = none
    rcases h_cons i with h | h <;> rcases hcons' i with h' | h'
    · -- e i = none from both sides
      exact h
    · -- e i = none and e i = some (c' i): contradiction
      exact h
    · -- e i = some (c i) and e i = none: contradiction
      rw [h] at h'; exact absurd h' (by simp)
    · -- e i = some (c i) and e i = some (c' i) → c i = c' i, contradicting hi
      have : c i = c' i := Option.some.inj (h.symm.trans h')
      exact absurd this hi
  -- d ≤ d(c, c') ≤ numErasures e ≤ d-1: contradicts d(c,c') ≥ 1.
  have h_ge : d ≤ hammingDist c c' := h_dist c hc c' hc' (Ne.symm hne)
  have h_pos : 1 ≤ hammingDist c c' :=
    Nat.one_le_iff_ne_zero.mpr (by simp [hammingDist_eq_zero]; exact fun h => hne h.symm)
  -- Chain: 1 ≤ hammingDist ≤ numErasures ≤ d - 1, so 1 ≤ d - 1 < d.
  -- Also d ≤ hammingDist ≤ numErasures ≤ d - 1, so d ≤ d - 1.
  -- Both together give 1 ≤ d and d ≤ d - 1, contradicting each other.
  have h_chain : 1 ≤ d - 1 := Nat.le_trans h_pos (Nat.le_trans h_sub h_era)
  have h2 : d ≤ d - 1 := Nat.le_trans h_ge (Nat.le_trans h_sub h_era)
  omega

/-!
### Erasure Decoding Algorithm

Given a code (as a list) and an erased word, find the unique codeword
consistent with all unerased positions. Returns `none` if no codeword
is consistent, or `some c` for the (unique) consistent codeword.
-/

/-- Computable erasure decoder: scan the codeword list for the first codeword
    consistent with the erased received word (agreeing on every `some` position).
    Uses `List.ofFn` to iterate over all n positions without needing `Finset.toList`. -/
def decodeErasureEval {n : ℕ} {α : Type*} [DecidableEq α]
    (codewords : List (Fin n → α)) (e : Fin n → Option α) : Option (Fin n → α) :=
  codewords.find? (fun c =>
    -- Build the list [(e 0, c 0), (e 1, c 1), ..., (e (n-1), c (n-1))] and check all.
    (List.ofFn (fun i : Fin n => (e i, c i))).all (fun (ec : Option α × α) =>
      match ec.1 with
      | none   => true
      | some a => a == ec.2))

/-!
### Erasure Decoding Examples
-/

-- ── Repetition code erasure decoding ─────────────────────────────────────

-- The [3,1,3] repetition code has min dist 3, so it corrects up to 2 erasures.

-- Sent: 111, positions 0 and 2 erased → received: ?1?
-- Only codeword consistent with "middle bit = 1" is 111.
#eval decodeErasureEval repCode3 (![none, some true, none] : Fin 3 → Option Bool)
-- Expected: some (fun _ => true)

-- Sent: 000, position 1 erased → received: 0?0
#eval decodeErasureEval repCode3 (![some false, none, some false] : Fin 3 → Option Bool)
-- Expected: some (fun _ => false)

-- ── [7,4,3] Hamming code erasure decoding ─────────────────────────────────

-- The [7,4,3] code has min dist 3, so it corrects up to 2 erasures.

-- Sent: 0000000, positions 3 and 5 erased → received: 000?0?0
#eval decodeErasureEval hammingCode74List
  (![some false, some false, some false, none, some false, none, some false] : Fin 7 → Option Bool)
-- Expected: some (fun _ => false)

-- Sent: 1101001, position 0 erased → received: ?101001
#eval decodeErasureEval hammingCode74List
  (![none, some true, some false, some true, some false, some false, some true] : Fin 7 → Option Bool)
-- Expected: some ![true, true, false, true, false, false, true]

end ErrorCorrection

/-! ─────────────────────────────────────────────────────────────────────────
## Part 4: The Hamming Bound (Sphere-Packing Bound)
──────────────────────────────────────────────────────────────────────────── -/

section HammingBound

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {n : ℕ}

/-!
### The Hamming Ball Volume Formula

The size of a Hamming ball of radius t in the n-dimensional space α^n (with
|α| = q) is:

    V(n, t, q) = Σ_{i=0}^{t} C(n, i) · (q-1)^i

**Why?** To form a word w with d(u, w) = i (exactly i positions differ):
* Choose which i positions differ: C(n, i) ways
* For each differing position, choose one of (q-1) symbols ≠ u_j: (q-1)^i ways
Summing over i = 0, 1, …, t gives the total.
-/

/-- The volume of a Hamming ball: Σ_{i=0}^{t} C(n, i) · (q-1)^i -/
def ballVol (n t q : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (t + 1), Nat.choose n i * (q - 1) ^ i

-- For binary (q = 2) and small n, t:
#eval ballVol 3 1 2  -- 4  (= C(3,0) + C(3,1) = 1 + 3)
#eval ballVol 7 1 2  -- 8  (= C(7,0) + C(7,1) = 1 + 7)
#eval ballVol 7 3 2  -- 64 (= 1 + 7 + 21 + 35)

/-!
### Statement of the Hamming Bound

**Theorem (Hamming Bound):**
Any (n, M, d)-code over an alphabet of size q, with d ≥ 2t+1, satisfies:

    M · V(n, t, q) ≤ q^n

**Proof:**
1. The M balls of radius t around codewords are pairwise disjoint (by the
   disjointness lemma above).
2. Each ball has size V(n, t, q) (the volume formula).
3. All balls are contained in α^n, which has q^n elements.
4. Therefore M · V(n, t, q) ≤ q^n.
-/

-- A key ingredient: all Hamming balls of the same radius have the same size.
-- (Follows from the fact that the Hamming metric is translation-invariant:
-- d(u,v) = d(u+w, v+w) when α is a group — but the counting argument works
-- for any alphabet.)
lemma hammingBall_card (u : Codeword n α) (r : ℕ) :
    (hammingBall u r).card = ballVol n r (Fintype.card α) := by
  simp [hammingBall, ballVol]
  -- This is a combinatorial fact: the ball of radius r has the same size
  -- regardless of the center u, since the alphabet is uniform.
  sorry

/-- The Hamming Bound: for a t-error-correcting code with M codewords,
    M · V(n, t, q) ≤ q^n. -/
theorem hamming_bound (C : Code n α) (t : ℕ)
    (h_dist : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → 2 * t + 1 ≤ hammingDist u v) :
    C.card * ballVol n t (Fintype.card α) ≤ (Fintype.card α) ^ n := by
  -- Step 1: The balls are pairwise disjoint.
  have h_disj : ∀ u ∈ C, ∀ v ∈ C, u ≠ v →
      Disjoint (hammingBall u t) (hammingBall v t) :=
    hammingBalls_disjoint C t h_dist

  -- Step 2: The total space has (Fintype.card α)^n elements.
  have hspace : Fintype.card (Codeword n α) = (Fintype.card α) ^ n := by
    simp [Codeword, Fintype.card_pi, Fintype.card_fin]

  -- Step 3: All balls have the same size V(n, t, q).
  -- Step 4: The union of disjoint balls fits in the full space.
  -- (Formal proof left as a sorry; the key steps are outlined above.)
  sorry

end HammingBound

/-! ─────────────────────────────────────────────────────────────────────────
## Part 5: The Singleton Bound
──────────────────────────────────────────────────────────────────────────── -/

section SingletonBound

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {n : ℕ}

/-!
### Statement of the Singleton Bound

**Theorem (Singleton Bound, 1964):**
Any (n, M, d)-code over an alphabet of size q satisfies:

    M ≤ q^(n-d+1)

**Proof (puncturing argument):**
Define the projection map f : α^n → α^(n-d+1) by f(c) = (c₁, c₂, …, c_{n-d+1}).
We claim f is injective on C.

Suppose f(c₁) = f(c₂) for c₁ ≠ c₂ in C. Then c₁ and c₂ agree on the first
n-d+1 positions, so they can only differ in the remaining d-1 positions.
Therefore d(c₁, c₂) ≤ d-1, contradicting min dist ≥ d.

Since f is injective on C and the range has size q^(n-d+1), we get |C| ≤ q^(n-d+1).

Note: A code achieving equality M = q^(n-d+1) is called an **MDS code**
(Maximum Distance Separable). Reed-Solomon codes are the most famous examples.
-/

/-- Projection onto the first k coordinates. -/
def project (k : ℕ) (hk : k ≤ n) (c : Codeword n α) : Codeword k α :=
  fun i => c (Fin.castLE hk i)

/-- If two codewords have Hamming distance ≥ d, their projections onto
    the first (n - d + 1) coordinates must be distinct. -/
lemma project_ne_of_large_dist (d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n)
    (u v : Codeword n α) (h_dist : hammingDist u v ≥ d) (h_neq : u ≠ v) :
    project (n - d + 1) (by omega) u ≠ project (n - d + 1) (by omega) v := by
  intro h_proj_eq
  -- The projections agree, so u and v agree on the first n-d+1 positions.
  have h_agree : ∀ i : Fin (n - d + 1),
      u (Fin.castLE (by omega) i) = v (Fin.castLE (by omega) i) := fun i =>
    congr_fun h_proj_eq i
  -- Therefore u and v only differ in positions ≥ n-d+1.
  -- The set of disagreement positions is a subset of {n-d+1, …, n-1}.
  -- That set has cardinality d-1.
  -- So d(u,v) ≤ d-1 < d — contradicting h_dist.
  -- (The formal accounting of cardinality uses Finset.Ico and Finset.card_le_card.)
  have h_dist_le : hammingDist u v ≤ d - 1 := by
    sorry
  omega

/-- The Singleton Bound: |C| ≤ |α|^(n-d+1). -/
theorem singleton_bound (C : Code n α) (d : ℕ)
    (hd : 1 ≤ d) (hdn : d ≤ n)
    (h_minDist : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → hammingDist u v ≥ d) :
    C.card ≤ (Fintype.card α) ^ (n - d + 1) := by
  -- Use the projection map f(c) = first (n-d+1) coordinates of c.
  let f : Codeword n α → Codeword (n - d + 1) α := project (n - d + 1) (by omega)
  -- Show f is injective on C.
  have h_inj : Set.InjOn f C := by
    intro u hu v hv h_feq
    by_contra h_neq
    exact project_ne_of_large_dist d hd hdn u v
      (h_minDist u hu v hv h_neq) h_neq h_feq
  -- The image of f has size |α|^(n-d+1).
  calc C.card
      ≤ (Finset.univ (α := Codeword (n - d + 1) α)).card := by
        apply Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) h_inj
    _ = (Fintype.card α) ^ (n - d + 1) := by
        simp [Codeword, Fintype.card_pi, Fintype.card_fin]

end SingletonBound

/-! ─────────────────────────────────────────────────────────────────────────
## Part 6: Exercises
──────────────────────────────────────────────────────────────────────────── -/

section Exercises

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {n : ℕ}

/-!
### Exercise 1 (Homework): Hamming Distance is Symmetric

Prove symmetry: d(u, v) = d(v, u) using our definition `hammingDist'`.

**Hint:** Show the two Finsets {i | u i ≠ v i} and {i | v i ≠ u i} are equal.
-/
lemma hammingDist'_comm (u v : Codeword n α) :
    hammingDist' u v = hammingDist' v u := by
  sorry

/-!
### Exercise 2 (Homework): Hamming Distance Triangle Inequality

Prove that `hammingDist'` satisfies the triangle inequality.

**Hint:** If u i ≠ w i, then either u i ≠ v i or v i ≠ w i (or both).
Therefore {i | u i ≠ w i} ⊆ {i | u i ≠ v i} ∪ {i | v i ≠ w i}.
Use `Finset.card_le_card` and `Finset.card_union_le`.
-/
lemma hammingDist'_triangle (u v w : Codeword n α) :
    hammingDist' u w ≤ hammingDist' u v + hammingDist' v w := by
  sorry

/-!
### Exercise 3 (Homework): Minimum Distance of the Repetition Code

The binary repetition code of length n (n ≥ 2) has minimum distance n.

**Hint:** The only two codewords are the all-0 and all-1 words.
Count the positions where they differ: all n of them.
-/
lemma repetitionCode_minDist (n : ℕ) (hn : n ≥ 2) :
    hasMinDist (repetitionCode n) n := by
  sorry

/-!
### Exercise 4 (Homework): Error-Detection Capability

A code with minimum distance d can detect up to d-1 errors.

Formally: if c ∈ C is sent and r is received with 1 ≤ d(c, r) ≤ d-1, then r ∉ C.

**Hint:** If r ∈ C and d(c, r) ≥ 1 (so r ≠ c), then by the minimum distance
property, d(c, r) ≥ d. Contrapositive of what we want.
-/
lemma detects_dMinus1_errors (C : Code n α) (d : ℕ) (hd : 1 ≤ d)
    (h_minDist : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → hammingDist u v ≥ d)
    (c r : Codeword n α) (hc : c ∈ C)
    (h_errors : 1 ≤ hammingDist c r) (h_few : hammingDist c r ≤ d - 1) :
    r ∉ C := by
  sorry

end Exercises
