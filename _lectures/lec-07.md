---
layout: lecture
title: "Lecture 7: Algorithm Verification and Cryptography in Lean"
date: 2026-03-06
demo_url: https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fucb-lean-course-sp26%2Fucb-lean-course-sp26.github.io%2Frefs%2Fheads%2Fmain%2FLeanSource%2FDemos%2FLec7.lean
demo_sol_url: https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fucb-lean-course-sp26%2Fucb-lean-course-sp26.github.io%2Frefs%2Fheads%2Fmain%2FLeanSource%2FDemos%2FLec7sol.lean
---

* TOC
{:toc}

## Dependencies

The lecture demo depends on **[CSLib](https://www.cslib.io)**, the Lean library for Computer Science. Full install instructions are available at [https://github.com/leanprover/cslib/](https://github.com/leanprover/cslib/).

To add CSLib as a dependency to your Lean project, add the following to your `lakefile.toml`:

```toml
[[require]]
name = "cslib"
scope = "leanprover"
rev = "main"
```

Or if you're using `lakefile.lean`:

```lean
require cslib from git "https://github.com/leanprover/cslib" @ "main"
```

Then run `lake update cslib` to fetch the dependency. You can also use a release tag instead of `main` for the `rev` value.

## 1. Introduction

In previous lectures, we proved properties *about* mathematical objects — graph colorings, walks, and codes. In this lecture, we prove properties *about algorithms* from two very different domains: a classical sorting algorithm and a modern cryptographic system.

**Part 1 — Insertion Sort:** We use the `TimeM` monad to simultaneously verify that insertion sort is *correct* (it produces a sorted permutation of the input) and *efficient* (it performs at most $n^2$ comparisons).

**Part 2 — RSA Correctness:** We formalize the RSA public-key cryptosystem and prove its central correctness property: decrypting an encrypted message recovers the original. This brings together Fermat's Little Theorem, modular arithmetic in `ZMod`, and the Chinese Remainder Theorem — all from Mathlib.

### What We Will Cover

1. **The `TimeM` monad:** design, notation, and key lemmas
2. **Insertion sort:** the algorithm, functional correctness, and a quadratic time bound
3. **RSA correctness:** `ZMod`, the `Fact` typeclass, Fermat's Little Theorem, and CRT
4. **New Lean techniques:** `haveI`, `push_cast`, `map_natCast`, and bundled structures

## 2. The `TimeM` Monad

### 2.1 Structure

`TimeM T α` is a simple product type:

```lean
structure TimeM (T : Type*) (α : Type*) where
  ret  : α   -- the return value of the computation
  time : T   -- the accumulated cost (usually T = ℕ)
```

A `TimeM ℕ α` computation is just a pair of a result and a natural number cost. There is no actual execution, no effects — everything is **pure** and **total**. The "monad" structure tells us how to *compose* such computations: when we sequence two computations with `>>=`, their costs add.

```lean
protected def bind (m : TimeM T α) (f : α → TimeM T β) : TimeM T β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩
```

### 2.2 The `✓` Tick Notation

To charge one unit of time, we use the tick primitive:

```lean
def tick (c : T) : TimeM T PUnit := ⟨.unit, c⟩
```

In `do`-notation, `✓` means "charge 1 unit of time and continue". So when we write `✓; return x` in a `do`-block, the resulting computation has `ret = x` and `time = 1`.

### 2.3 The `⟪·⟫` Notation

To extract just the return value from a `TimeM` computation, we write `⟪m⟫`:

```lean
notation:max "⟪" tm "⟫" => TimeM.ret tm
```

This is the key to our **separation of concerns**:

| Projection | What it gives | Used for |
|---|---|---|
| `⟪m⟫` | The pure result `m.ret` | Correctness theorems |
| `m.time` | The accumulated cost | Complexity theorems |

### 2.4 Key `simp` Lemmas

```lean
@[simp] theorem ret_pure  (a : α) : (pure a : TimeM T α).ret  = a              := rfl
@[simp] theorem ret_bind  (m) (f) : (m >>= f).ret             = (f m.ret).ret  := rfl
@[simp] theorem time_pure (a : α) : (pure a : TimeM T α).time = 0              := rfl
@[simp] theorem time_bind (m) (f) : (m >>= f).time            = m.time + (f m.ret).time := rfl
@[simp] theorem time_tick (c : T) : (tick c).time             = c              := rfl
```

## 3. Insertion Sort

### 3.1 The Algorithm

We implement insertion sort over an ordered type `α` with `[LinearOrder α]`.

**`insert x xs`** inserts element `x` into an already-sorted list `xs`, charging one tick per comparison:

```lean
def insert (x : α) : List α → TimeM ℕ (List α)
  | [] =>
      return [x]
  | y :: ys => do
      ✓                          -- charge one comparison
      if x ≤ y then
        return x :: y :: ys
      else
        let zs ← insert x ys
        return y :: zs
```

**`insertionSort xs`** sorts `xs` by inserting each element into the sorted tail:

```lean
def insertionSort : List α → TimeM ℕ (List α)
  | [] =>
      return []
  | x :: xs => do
      let ys ← insertionSort xs
      insert x ys
```

### 3.2 Connecting to Mathlib

Mathlib provides `List.orderedInsert` and `List.insertionSort` as pure functions. We bridge to them with two `@[simp]` lemmas:

```lean
@[simp] theorem ret_insert (x : α) (xs : List α) :
    ⟪insert x xs⟫ = List.orderedInsert (· ≤ ·) x xs

@[simp] theorem ret_insertionSort (xs : List α) :
    ⟪insertionSort xs⟫ = List.insertionSort (· ≤ ·) xs
```

Once these bridges are proved, **all correctness properties follow by `simpa`**, delegating to Mathlib:

```lean
theorem insertionSort_perm (xs : List α) :
    ⟪insertionSort xs⟫ ~ xs := by
  simpa [ret_insertionSort] using List.perm_insertionSort (· ≤ ·) xs

theorem insertionSort_sorted (xs : List α) :
    IsSorted ⟪insertionSort xs⟫ := by
  simpa [ret_insertionSort, IsSorted] using
    List.pairwise_insertionSort (· ≤ ·) xs
```

### 3.3 Time Complexity

**Step 1: bound `insert`.**

```lean
theorem time_insert_le (x : α) (xs : List α) :
    (insert x xs).time ≤ xs.length
```

*Proof:* Induction on `xs`. The `nil` case is trivial. In the `cons y ys` case, both branches charge 1 tick and the else-branch recurses; the inductive hypothesis closes with `omega`.

**Step 2: bound `insertionSort` via a recurrence.**

```lean
def timeInsertionSortRec : Nat → Nat
  | 0     => 0
  | n + 1 => timeInsertionSortRec n + n

theorem time_insertionSort_le_rec (xs : List α) :
    (insertionSort xs).time ≤ timeInsertionSortRec xs.length
```

**Step 3: close with a quadratic bound.**

```lean
theorem timeInsertionSortRec_le_sq (n : Nat) :
    timeInsertionSortRec n ≤ n * n
```

*Proof:* By induction. The `succ` case unfolds the recurrence with `simp only` and closes with `nlinarith`:

$$T(n+1) = T(n) + n \leq n^2 + n \leq (n+1)^2$$

**Putting it together:**

```lean
theorem time_insertionSort_le_sq (xs : List α) :
    (insertionSort xs).time ≤ xs.length * xs.length :=
  le_trans (time_insertionSort_le_rec xs) (timeInsertionSortRec_le_sq xs.length)
```

## 4. RSA Algorithm Correctness

### 4.1 Background

The RSA cryptosystem works as follows. Choose distinct primes $p$ and $q$, set $n = pq$, and pick exponents $e$ and $d$ satisfying:

$$e \cdot d \equiv 1 \pmod{(p-1)(q-1)}$$

In Lean we represent this as the existence of a witness $k$ such that $e \cdot d = 1 + k(p-1)(q-1)$.

**Encryption:** $\text{Enc}(m) = m^e \bmod n$

**Decryption:** $\text{Dec}(c) = c^d \bmod n$

**Correctness claim:** $\text{Dec}(\text{Enc}(m)) = m \bmod n$ for all messages $m$.

The proof uses three mathematical ingredients:
1. **Fermat's Little Theorem:** $x^p = x$ in $\mathbb{Z}/p\mathbb{Z}$ for prime $p$
2. **Exponent decomposition:** $m^{ed} \equiv m$ mod $p$ and mod $q$ separately
3. **Chinese Remainder Theorem:** these two congruences together give $m^{ed} \equiv m$ mod $pq$

### 4.2 `ZMod` and the `Fact` Typeclass

Lean's `ZMod n` is the type of integers modulo `n`. For a prime `p`, `ZMod p` is a field; in particular, elements satisfy Fermat's little theorem.

Many Mathlib lemmas about `ZMod p` require primality of `p` as a **typeclass argument** `[Fact p.Prime]` rather than an explicit hypothesis. The `Fact` wrapper is a single-field structure used to inject propositions into the typeclass system:

```lean
structure Fact (p : Prop) : Prop where
  out : p
```

When primality is available as a plain hypothesis `hp : p.Prime`, you install it as a local instance with `haveI`:

```lean
haveI fact_p : Fact key.p.Prime := ⟨key.hp⟩
```

After this line, any lemma requiring `[Fact key.p.Prime]` will find the instance automatically.

### 4.3 Fermat's Little Theorem: `rsa_core`

The key algebraic lemma is:

```lean
lemma rsa_core (p : ℕ) [hp : Fact p.Prime] (c : ℕ) (x : ZMod p) :
    x ^ (1 + c * (p - 1)) = x
```

This says that in `ZMod p`, raising to a power of the form $1 + c(p-1)$ is the identity.

**Why induct on `c` instead of using Fermat directly?**
Fermat's little theorem (`ZMod.pow_card : x ^ p = x`) handles $x = 0$ automatically. If instead we used the unit-group version $x^{p-1} = 1$, we would need to split on whether $x = 0$. Inducting on $c$ avoids this entirely.

**The induction:**

*Base case ($c = 0$):* $x^{1 + 0 \cdot (p-1)} = x^1 = x$. ✓

*Inductive step ($c \to c+1$):*

$$x^{1 + (c+1)(p-1)} = x^{1 + c(p-1) + (p-1)} = x^{1+c(p-1)} \cdot x^{p-1}$$

By the inductive hypothesis, $x^{1+c(p-1)} = x$, so:

$$x \cdot x^{p-1} = x^p \stackrel{\text{FLT}}{=} x$$

In Lean, the exponent rearrangement is done with three rewrites, then `mul_comm` + `← pow_succ` turns `x * x^(p-1)` into `x^p`, and `ZMod.pow_card` closes the goal:

```lean
  | succ c ih =>
    have heq : 1 + (c + 1) * (p - 1) = 1 + c * (p - 1) + (p - 1) := by
      rw [add_mul, one_mul, add_assoc]
    rw [heq, pow_add, ih, mul_comm, ← pow_succ]
    have : p - 1 + 1 = p := by have := hp.out.two_le; omega
    rw [this]; exact ZMod.pow_card x
```

### 4.4 Lifting to Both Prime Factors

The bridge between `rsa_core` and the RSA exponent condition goes through a small generic helper:

```lean
lemma rsa_zmod_of_factor (p : ℕ) [Fact p.Prime]
    (m ed c : ℕ) (h : ed = 1 + c * (p - 1)) :
    ((m ^ ed : ℕ) : ZMod p) = (m : ZMod p)
```

This lemma says: if the exponent `ed` already has the form `1 + c*(p-1)`, then $m^{ed} \equiv m \pmod{p}$. The proof first converts the goal to a `ZMod p`-power statement via `push_cast`, applies `rsa_core`, then converts back.

Given `h_ed : e * d = 1 + k * (p - 1) * (q - 1)`, we apply the helper modulo each prime. For `p`, the exponent must be recast as `1 + (k*(q-1)) * (p-1)`:

```lean
lemma rsa_zmod_p {p q m e d k : ℕ} [Fact p.Prime]
    (h_ed : e * d = 1 + k * (p - 1) * (q - 1)) :
    ((m ^ (e * d) : ℕ) : ZMod p) = (m : ZMod p) := by
  have h' : e * d = 1 + (k * (q - 1)) * (p - 1) := by
    calc e * d = 1 + k * (p - 1) * (q - 1) := h_ed
      _ = 1 + k * (q - 1) * (p - 1) := by
          simp [Nat.mul_right_comm, Nat.mul_assoc]
  exact rsa_zmod_of_factor p m (e * d) (k * (q - 1)) h'
```

For `q`, the exponent is already in the right form (`1 + (k*(p-1)) * (q-1)`), so only a `simpa [Nat.mul_assoc]` is needed:

```lean
lemma rsa_zmod_q {p q m e d k : ℕ} [Fact q.Prime]
    (h_ed : e * d = 1 + k * (p - 1) * (q - 1)) :
    ((m ^ (e * d) : ℕ) : ZMod q) = (m : ZMod q) := by
  have h' : e * d = 1 + (k * (p - 1)) * (q - 1) := by
    simpa [Nat.mul_assoc] using h_ed
  exact rsa_zmod_of_factor q m (e * d) (k * (p - 1)) h'
```

### 4.5 The Chinese Remainder Theorem Step

With $m^{ed} \equiv m$ established mod $p$ and mod $q$ separately, we lift to mod $pq$ using Mathlib's CRT ring isomorphism:

```lean
ZMod.chineseRemainder : p.Coprime q → ZMod (p * q) ≃+* ZMod p × ZMod q
```

This is a `RingEquiv` — a ring isomorphism. To use it, we apply its injectivity: two elements of `ZMod (p * q)` are equal iff their images under the isomorphism are equal.

```lean
lemma rsa_crt {p q m ed : ℕ} (hpq : p.Coprime q)
    (hp : ((m ^ ed : ℕ) : ZMod p) = (m : ZMod p))
    (hq : ((m ^ ed : ℕ) : ZMod q) = (m : ZMod q)) :
    ((m ^ ed : ℕ) : ZMod (p * q)) = (m : ZMod (p * q)) := by
  apply (ZMod.chineseRemainder hpq).injective
  simp only [map_natCast]
  ext <;> assumption
```

**`map_natCast`** is the key lemma: any ring homomorphism `f : R →+* S` satisfies `f (n : ℕ) = (n : S)`. Since `ZMod.chineseRemainder` is a `RingEquiv` (which coerces to a ring hom), `simp only [map_natCast]` rewrites both sides to their canonical forms.

The main theorem ultimately needs to state the result as a `ZMod`-power equality — `(m : ZMod (p*q)) ^ ed = m` — rather than a casted `ℕ`-power. For this we have a companion lemma that wraps `rsa_crt` with `push_cast` conversions:

```lean
lemma rsa_crt_pow {p q m ed : ℕ} (hpq : p.Coprime q)
    (hp : ((m : ZMod p) ^ ed) = (m : ZMod p))
    (hq : ((m : ZMod q) ^ ed) = (m : ZMod q)) :
    ((m : ZMod (p * q)) ^ ed) = (m : ZMod (p * q))
```

The proof converts `hp`/`hq` into the "casted Nat power" shape expected by `rsa_crt` (via `simpa [Nat.cast_pow]`), applies `rsa_crt`, then converts the conclusion back.

**Coprimality** of distinct primes is derived by contradiction: if $p \mid q$ and $q$ is prime, then $p = 1$ (ruled out by `p.Prime.ne_one`) or $p = q$ (ruled out by `hpq_neq`).

### 4.6 Key Structures and Main Theorem

RSA is split into two structures reflecting the real-world distinction between the public key (known to everyone) and the secret key (held only by the recipient):

```lean
/-- Public key: modulus and public exponent. -/
structure PublicKey where
  n : ℕ
  e : ℕ

/-- Secret key: ties the private exponent and prime factors to a public key. -/
structure SecretKey where
  pub     : PublicKey
  p  q  d  k : ℕ
  hp      : p.Prime
  hq      : q.Prime
  hpq_neq : p ≠ q
  hn      : pub.n = p * q
  h_ed    : pub.e * d = 1 + k * (p - 1) * (q - 1)
```

This is more realistic than a single bundled record: encryption takes only `PublicKey`; decryption requires `SecretKey`. The secret key carries a `pub` field so both operations work over the same modulus `pub.n`.

```lean
def encrypt (pub : PublicKey) (m : ℕ) : ZMod pub.n :=
  (m : ZMod pub.n) ^ pub.e

def decrypt (sec : SecretKey) (c : ZMod sec.pub.n) : ZMod sec.pub.n :=
  c ^ sec.d
```

The main correctness theorem assembles all the lemmas. After `push_cast` converts the `mod p` and `mod q` hypotheses into `ZMod`-power form, `rsa_crt_pow` closes the goal directly:

```lean
theorem rsa_correctness (sec : SecretKey) (m : ℕ) :
    decrypt sec (encrypt sec.pub m) = (m : ZMod sec.pub.n) := by
  dsimp [decrypt, encrypt]; rw [← pow_mul, sec.hn]
  haveI : Fact sec.p.Prime := ⟨sec.hp⟩
  haveI : Fact sec.q.Prime := ⟨sec.hq⟩
  have hp_eq := rsa_zmod_p (m := m) sec.h_ed   -- m ^ (e*d) ≡ m  (mod p)
  have hq_eq := rsa_zmod_q (m := m) sec.h_ed   -- m ^ (e*d) ≡ m  (mod q)
  push_cast at hp_eq hq_eq
  -- hp_eq : (m : ZMod sec.p) ^ (e*d) = m,  hq_eq : similarly mod q
  have hpq_coprime : sec.p.Coprime sec.q := by
    apply (Nat.Prime.coprime_iff_not_dvd sec.hp).2
    intro h_dvd
    rcases sec.hq.eq_one_or_self_of_dvd sec.p h_dvd with h | h
    · exact sec.hp.ne_one h
    · exact sec.hpq_neq h
  exact rsa_crt_pow hpq_coprime hp_eq hq_eq
```

Note that `haveI` is used without a name here — Lean just needs the instance to exist, not to be referenced later. The coprimality proof uses `Nat.Prime.ne_one` to rule out `p = 1` cleanly, without any manual `omega`.

## 5. Proof Techniques Summary

### 5.1 Separating `.ret` and `.time` Proofs

The `TimeM` design enables clean separation:

```lean
-- Correctness: reason about ⟪algorithm⟫
theorem algorithm_correct : ⟪myAlgo xs⟫ = expectedResult xs := by
  simpa [ret_myAlgo] using Mathlib.pure_result xs

-- Complexity: reason about algorithm.time
theorem algorithm_time : (myAlgo xs).time ≤ bound xs.length := by
  induction xs with ...
```

Each theorem focuses on exactly one concern. Correctness proofs leverage the full Mathlib library; complexity proofs reason about natural number arithmetic.

### 5.2 Bridging Timed Algorithms to Mathlib

Write a `@[simp]` bridge lemma connecting the timed version to a pure Mathlib function:

```lean
@[simp] theorem ret_algorithm (xs) : ⟪timedAlgorithm xs⟫ = Mathlib.pureAlgorithm xs
```

Once proved, all correctness properties follow by `simpa [ret_algorithm]`.

### 5.3 The `Fact` Typeclass and `haveI`

Mathlib frequently uses `[Fact p.Prime]` instead of `(hp : p.Prime)` to make primality available to the typeclass search engine. When you have an explicit proof `hp : p.Prime` and need to use a lemma requiring `[Fact p.Prime]`, install a local instance with:

```lean
haveI fact_p : Fact key.p.Prime := ⟨key.hp⟩
```

`haveI` is like `have` but registers the binding as a local typeclass instance. After this line, every lemma requiring `[Fact key.p.Prime]` will find it automatically.

Compare:

| Syntax | Effect |
|---|---|
| `have h : T := ...` | Introduces `h` as a local hypothesis only |
| `haveI h : T := ...` | Introduces `h` as a local hypothesis **and** a typeclass instance |

### 5.4 `push_cast` for Natural Number Casts

When working with `ZMod`, goals often involve expressions like `((m ^ e : ℕ) : ZMod p)` — a power computed in `ℕ` and then cast. Lemmas like `rsa_core` operate on `(m : ZMod p) ^ e` — a power computed in `ZMod p`. These are definitionally equal but syntactically different.

`push_cast` rewrites the goal to push coercions inward:

```lean
((m ^ e : ℕ) : ZMod p)
-- after push_cast becomes:
(m : ZMod p) ^ e
```

This transformation is always valid (ring homomorphisms preserve powers), and it lets you apply algebraic lemmas stated in `ZMod p` to goals involving `ℕ` casts.

### 5.5 `map_natCast` for Ring Equivalences

Any ring homomorphism `f : R →+* S` satisfies the lemma:

```lean
map_natCast : ∀ (n : ℕ), f (n : R) = (n : S)
```

This is crucial in `rsa_crt`: we need to know that the CRT isomorphism `f : ZMod (p * q) ≃+* ZMod p × ZMod q` sends natural number casts to natural number casts. `simp only [map_natCast]` applies this uniformly to both sides of the goal, reducing the problem to the component-wise equalities `hp` and `hq`.

### 5.6 Splitting Structures for Realistic APIs

The `PublicKey` / `SecretKey` pair is a common Lean pattern for formalizing systems where different operations need different subsets of data:

- **`PublicKey`** carries only what encryption needs (`n`, `e`) — no secrets exposed
- **`SecretKey`** nests a `pub : PublicKey` field and adds the private data and proof obligations

This is preferable to a single monolithic record because:
1. `encrypt` takes only a `PublicKey` — its type accurately reflects that no secret is needed
2. `decrypt` takes a `SecretKey`, which carries `pub` internally — no argument duplication
3. The separation makes it obvious which theorems require secret knowledge and which don't

## 6. Homework Exercises

### Exercise 1: Construct a Concrete RSA Key

Choose $p = 5$, $q = 11$, $n = 55$, $e = 3$, $d = 27$, $k = 2$. Construct a `SecretKey` with `decide` proofs:

```lean
def exampleKey : SecretKey where
  pub     := { n := 55, e := 3 }
  p := 5;  q := 11;  d := 27;  k := 2
  hp      := by decide
  hq      := by decide
  hpq_neq := by decide
  hn      := by decide
  h_ed    := by decide
```

Use `#eval` to encrypt and decrypt a sample message, then confirm `rsa_correctness` applies:

```lean
#eval (encrypt exampleKey.pub 7).val          -- expected: 13
#eval (decrypt exampleKey ⟨13, by decide⟩).val  -- expected: 7
```

### Exercise 2: `rsa_core` with an Explicit Primality Hypothesis

State and prove a version of `rsa_core` that takes an explicit `hp : p.Prime` instead of `[Fact p.Prime]`:

```lean
lemma rsa_core' (p : ℕ) (hp : p.Prime) (c : ℕ) (x : ZMod p) :
    x ^ (1 + c * (p - 1)) = x
```

**Hint:** Use `haveI : Fact p.Prime := ⟨hp⟩` at the start of the proof body to convert the explicit hypothesis into a typeclass instance, then apply `rsa_core`.

### Exercise 3: Encryption is Injective Modulo `n`

Use `rsa_correctness` to prove that two natural numbers with the same encryption must be congruent modulo `n`:

```lean
theorem encrypt_injective_mod (sec : SecretKey) (m₁ m₂ : ℕ)
    (h : encrypt sec.pub m₁ = encrypt sec.pub m₂) :
    (m₁ : ZMod sec.pub.n) = (m₂ : ZMod sec.pub.n)
```

**Hint:** Apply `rsa_correctness key m₁` and `rsa_correctness key m₂`. After unfolding, both `decrypt key (encrypt key m₁)` and `decrypt key (encrypt key m₂)` simplify to `(m₁ : ZMod key.n)` and `(m₂ : ZMod key.n)`. Use the hypothesis `h` and `congr_arg` to link them.

### Exercise 4: Insertion Sort Lower Bound

Prove that insertion sort on the reversed list `[n-1, n-2, ..., 1, 0]` performs exactly $n(n-1)/2$ comparisons:

```lean
def revList (n : ℕ) : List (Fin n) :=
  (List.range n).reverse.map (⟨·, by omega⟩)

theorem time_insertionSort_rev (n : ℕ) :
    (insertionSort (revList n)).time = n * (n - 1) / 2
```

**Hint:** First prove that inserting the $k$-th element of `revList` costs exactly $k$ comparisons (every comparison goes to the else-branch). Then induct on `n`.

## 7. Summary

In this lecture, we:

* Used `TimeM T α` for **simultaneous** computation and cost tracking, and proved insertion sort is correct and runs in $O(n^2)$ comparisons
* Formalized **RSA correctness** via Fermat's Little Theorem and the Chinese Remainder Theorem, all assembled from Mathlib
* Learned the `haveI` pattern for installing local typeclass instances from explicit hypotheses
* Used `push_cast` to reconcile `ℕ`-level computations with `ZMod`-level algebra
* Used `map_natCast` to transport equalities through ring isomorphisms
* Packaged data and proofs together in `structure` (the `PublicKey` / `SecretKey` types)

### Two Styles of Formal Verification

The two halves of this lecture illustrate two distinct proof styles:

| Style | Example | Key tools |
|---|---|---|
| **Algorithmic** — track cost, connect to pure spec | Insertion sort | `TimeM`, `simpa`, induction, `omega` |
| **Algebraic** — compose Mathlib lemmas, manage casts | RSA | `ZMod`, `Fact`, `push_cast`, `map_natCast`, CRT |

Both styles are common in Lean formalization. The algorithmic style is typical in verified algorithm libraries; the algebraic style is typical in formalized number theory and cryptography.

### Connections to Previous Lectures

* **Lectures 1–3:** `by_cases`, `omega`, `simp`, and `calc` are used throughout both parts
* **Lecture 4:** Decision trees also count comparisons — `TimeM` generalizes that counting framework
* **Lecture 5:** `Finset`-based arguments appear again in the CRT isomorphism
* **Lecture 6:** Error-correcting codes and RSA both draw on algebra over finite fields and modular arithmetic

### Further Directions

* **Merge sort:** An $O(n \log n)$ sorting algorithm that fits naturally into `TimeM`
* **Euler's theorem:** Generalize RSA correctness from $(p-1)(q-1)$ to Euler's $\phi(n)$, using `Nat.totient` from Mathlib
* **Miller–Rabin primality test:** A probabilistic algorithm whose correctness involves modular arithmetic and Fermat witnesses
* **Digital signatures:** The RSA signature scheme reuses the same algebra but in the opposite direction
* **Elliptic curve cryptography:** A more modern approach to public-key crypto, formalized using Mathlib's `EllipticCurve` library
