---
layout: lecture
title: "Lecture 6: Introduction to Coding Theory in Lean"
date: 2026-02-27
demo_url: https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fucb-lean-course-sp26%2Fucb-lean-course-sp26.github.io%2Frefs%2Fheads%2Fmain%2FLeanSource%2FDemos%2FLec6.lean
---

* TOC
{:toc}

## 1. Introduction

In this lecture, we introduce **error-correcting codes** — one of the most beautiful and practically important topics in theoretical computer science and applied mathematics. Coding theory was born in 1948 with Claude Shannon's landmark paper "A Mathematical Theory of Communication," and has since grown into a rich field connecting combinatorics, algebra, probability, and algorithms.

**What is the problem?** When transmitting data over a noisy channel (a wireless link, a hard drive, a QR code, deep-space communication), some bits may be corrupted. Error-correcting codes allow us to add **redundancy** in a structured way so that the original message can be recovered even after some errors occur.

**Why formalize it in Lean?** Coding theory has beautiful combinatorial theorems with clean proof structures — ideal for formalization. Moreover, coding theory is increasingly relevant to TCS (probabilistically checkable proofs, locality, complexity theory) and cryptography.

### What We Will Cover

1. **Basic definitions:** codewords, codes, Hamming distance, minimum distance
2. **Example codes:** repetition code, parity check code, [7,4,3] Hamming code
3. **Error detection and correction:** how minimum distance governs capability, nearest-neighbor decoding, erasure correction
4. **The Hamming Bound:** a fundamental upper bound on code size
5. **The Singleton Bound:** another fundamental upper bound with a slick proof

Throughout, we formalize these concepts in Lean and prove key theorems.

## 2. Basic Definitions

### 2.1 Alphabets and Codewords

We work over an **alphabet** — a finite set of symbols. In practice:
* The **binary alphabet** `{0, 1}` (most common in engineering)
* A **q-ary alphabet** `{0, 1, …, q-1}` for prime power q

In Lean, we represent an alphabet as any finite type `α` with decidable equality:

```lean
variable {α : Type*} [Fintype α] [DecidableEq α]
```

A **codeword** of **length** n is a sequence of n alphabet symbols:

```lean
abbrev Codeword (n : ℕ) (α : Type*) := Fin n → α
```

So a codeword is just a function `Fin n → α` — a length-n sequence indexed by `{0, 1, …, n-1}`.

A **code** of length n is a finite set of codewords:

```lean
abbrev Code (n : ℕ) (α : Type*) := Finset (Codeword n α)
```

### 2.2 Hamming Distance

**Definition:** The **Hamming distance** between two codewords u and v of length n is the number of positions where they differ:

$$d(u, v) = \bigl|\{i \in \{0,\ldots,n-1\} \mid u_i \neq v_i\}\bigr|$$

**Example:**

```
u = 0 1 1 0 1
v = 0 0 1 1 1
      ^   ^     ← 2 positions differ
```

So $d(u, v) = 2$.

In Lean, using Mathlib's `hammingDist`:

```lean
#eval hammingDist (α := Bool) (n := 5)
        ![true, false, true, false, true]
        ![true, true,  true, true,  true]
-- Output: 2
```

For pedagogy, we also define it directly:

```lean
def hammingDist' (u v : Codeword n α) : ℕ :=
  (Finset.univ.filter (fun i => u i ≠ v i)).card
```

**Key properties of Hamming distance:**

1. **Non-negativity:** $d(u, v) \geq 0$, with equality iff $u = v$.
2. **Symmetry:** $d(u, v) = d(v, u)$.
3. **Triangle inequality:** $d(u, w) \leq d(u, v) + d(v, w)$.

These three properties make the Hamming metric a proper metric on $\alpha^n$.

### 2.3 Minimum Distance

**Definition:** The **minimum distance** of a code $C$ with $\lvert C \rvert \geq 2$ is:

$$d(C) = \min_{u, v \in C,\; u \neq v} d(u, v)$$

This is the *most important* parameter of a code. We say $C$ is an $(n, M, d)$**-code** if:
* $n$ = block length (codeword length)
* $M = \lvert C \rvert$ = number of codewords
* $d = d(C)$ = minimum distance

In Lean:

```lean
def hasMinDist (C : Code n α) (d : ℕ) : Prop :=
  (∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d) ∧
  (∀ u ∈ C, ∀ v ∈ C, u ≠ v → hammingDist u v ≥ d)
```

Note that `hasMinDist` asserts both **existence** (there is a pair at distance exactly d) and **minimality** (no pair is closer).

## 3. Example Codes

### 3.1 The Repetition Code

The simplest possible code: **repeat each bit n times**.

$$\text{Rep}_n : \{0, 1\} \to \{0, 1\}^n, \quad 0 \mapsto 0\cdots 0, \quad 1 \mapsto 1\cdots 1$$

The code $C = \{00\cdots 0,\; 11\cdots 1\}$ is an $(n, 2, n)$-code.

In Lean:

```lean
def repetitionCode (n : ℕ) : Code n Bool :=
  {(fun _ => false), (fun _ => true)}
```

**Properties:**
* Has 2 codewords (for $n \geq 1$)
* Minimum distance = $n$ (the two codewords differ in every position)
* Can correct $\lfloor (n-1)/2 \rfloor$ errors (majority voting)

```lean
#eval hammingDist (α := Bool) (n := 3) (fun _ => false) (fun _ => true)
-- Output: 3
```

### 3.2 The Parity Check Code

**Add one redundant bit** to detect single-bit errors.

The **binary parity code** of length $n$ consists of all binary words with an **even** number of 1s:

$$C_{\text{par}} = \{x \in \{0,1\}^n \mid x_1 + x_2 + \cdots + x_n \equiv 0 \pmod{2}\}$$

This is an $(n, 2^{n-1}, 2)$-code:
* Length $n$
* $2^{n-1}$ codewords (half of all $2^n$ binary strings)
* Minimum distance 2 (flipping any one bit changes parity, so any two codewords differ in at least 2 positions)

```lean
def parityCode (n : ℕ) : Code n Bool :=
  Finset.univ.filter (fun (c : Fin n → Bool) =>
    (Finset.univ.filter (fun i => c i = true)).card % 2 = 0)

#eval parityCode 3
-- The 4 binary words of length 3 with even # of 1s: {000, 011, 101, 110}
```

**What parity codes can do:**
* **Detect** 1 error (a single flip changes parity, so the received word is not a codeword)
* **Cannot correct** any error (we know an error occurred, but not where)

### 3.3 The Hamming Code

The **Hamming code** Ham$(r, 2)$ is a famous family of perfect binary codes:
* Length $n = 2^r - 1$
* $M = 2^{2^r - 1 - r}$ codewords
* Minimum distance $d = 3$

For $r = 2$: Ham$(2, 2)$ has length 3 and is just the triple repetition code (a $(3, 2, 3)$-code).

For $r = 3$: Ham$(3, 2)$ has length 7, $M = 16$ codewords, $d = 3$ (the famous $[7, 4, 3]$ Hamming code).

## 4. Error Detection and Correction

### 4.1 The Key Theorem

The relationship between minimum distance and error-correction capability is:

**Theorem:** A code with minimum distance $d$ can:
1. **Detect** up to $d - 1$ errors.
2. **Correct** up to $t = \lfloor (d-1)/2 \rfloor$ errors.

The formal proof uses Hamming balls.

### 4.2 Hamming Balls

**Definition:** The **Hamming ball** of radius $r$ centered at $u \in \alpha^n$ is:

$$B(u, r) = \{v \in \alpha^n \mid d(u, v) \leq r\}$$

In Lean:

```lean
def hammingBall (u : Codeword n α) (r : ℕ) : Finset (Codeword n α) :=
  Finset.univ.filter (fun v => hammingDist u v ≤ r)
```

**Intuition:** $B(u, r)$ is the set of all words that could have been received if $u$ was sent and at most $r$ errors occurred.

```lean
#eval (hammingBall (n := 3) (α := Bool) (fun _ => false) 1).card
-- Output: 4  (000, 001, 010, 100)
```

### 4.3 Why Minimum Distance Governs Correction

**Proof of t-error correction:**

Suppose $d(C) \geq 2t + 1$. We claim the Hamming balls $B(c, t)$ for $c \in C$ are pairwise disjoint.

**Proof of disjointness:** If $w \in B(u, t) \cap B(v, t)$, then $d(u, w) \leq t$ and $d(w, v) \leq t$. By the triangle inequality:

$$d(u, v) \leq d(u, w) + d(w, v) \leq t + t = 2t$$

But $d(u, v) \geq 2t + 1$ since $u, v$ are distinct codewords. Contradiction.

```lean
lemma hammingBalls_disjoint (C : Code n α) (t : ℕ)
    (h_dist : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → 2 * t + 1 ≤ hammingDist u v) :
    ∀ u ∈ C, ∀ v ∈ C, u ≠ v → Disjoint (hammingBall u t) (hammingBall v t)
```

The proof in Lean directly formalizes the triangle inequality argument:

```lean
  intro w hwu hwv
  simp [hammingBall] at hwu hwv
  have h_tri : hammingDist u v ≤ hammingDist u w + hammingDist w v :=
    hammingDist_triangle u w v
  have h_ge := h_dist u hu v hv huv
  omega
```

**Consequence:**
Given a received word $r$, the nearest codeword is unique (since balls don't overlap), and equals the sent codeword if $\leq t$ errors occurred.

This is formalized as the `error_correction` theorem:

```lean
theorem error_correction (C : Code n α) (t : ℕ)
    (h_dist : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → 2 * t + 1 ≤ hammingDist u v)
    (c r : Codeword n α) (hc : c ∈ C)
    (h_errors : hammingDist c r ≤ t) :
    ∀ c' ∈ C, c' ≠ c → hammingDist c' r > t
```

The proof is a direct `omega` chain: by the triangle inequality $d(c, c') \leq d(c, r) + d(r, c')$, and since $d(c, c') \geq 2t+1$ and $d(c, r) \leq t$, we get $d(c', r) \geq t+1$.

### 4.4 Nearest-Neighbor Decoding

The **nearest-neighbor decoder** finds the codeword closest to a received word $r$ in Hamming distance. This is the natural decoding strategy: given the correction guarantee above, the closest codeword must be the one that was sent (assuming $\leq t$ errors occurred).

We define two versions in Lean:

**Noncomputable version** (for theorem proving — uses `Finset.exists_min_image`):

```lean
noncomputable def decode (C : Code n α) (r : Codeword n α) : Option (Codeword n α) :=
  if h : C.Nonempty then
    some (C.exists_min_image (fun c => hammingDist c r) h).choose
  else none
```

**Computable version** (for `#eval` — scans the code as a list):

```lean
def decodeEval (codewords : List (Fin n → α)) (r : Fin n → α) : Option (Fin n → α) :=
  codewords.foldl
    (fun best c =>
      match best with
      | none   => some c
      | some b => if hammingDist c r < hammingDist b r then some c else best)
    none
```

**Decoding examples:**

```lean
-- Repetition code: sent 111, received 110 (one error)
#eval decodeEval repCode3 ![true, true, false]
-- Output: some (fun _ => true)  ✓

-- [7,4,3] code: sent 0000000, received 0000001 (one error at position 6)
#eval decodeEval hammingCode74List ![false, false, false, false, false, false, true]
-- Output: some (fun _ => false)  ✓
```

The `decode_mem` theorem confirms the noncomputable decoder always returns a member of $C$:

```lean
theorem decode_mem (C : Code n α) (r : Codeword n α) (c : Codeword n α)
    (h : decode C r = some c) : c ∈ C
```

### 4.5 Erasure Correction

An **erasure** is strictly different from an error: the receiver knows *which* positions were lost (e.g., a dropped packet), but not their values. This is easier to handle than errors because the locations are known.

**Key result:** A code with minimum distance $d$ can correct up to $d - 1$ erasures.

**Proof:** Suppose codeword $c$ was sent, and positions $E$ with $|E| \leq d-1$ were erased. If $c' \neq c$ is another codeword consistent with the received (partially erased) word, then $c$ and $c'$ agree on all unerased positions, so they can only differ on the $\leq d-1$ erased positions:

$$d(c, c') \leq |E| \leq d - 1 < d$$

contradicting the minimum distance.

We model erasures using `Option α`: `some a` means the position was received as symbol `a`, `none` means the position was erased.

```lean
abbrev ErasedWord (n : ℕ) (α : Type*) := Fin n → Option α

def consistent (c : Codeword n α) (e : ErasedWord n α) : Prop :=
  ∀ i, e i = none ∨ e i = some (c i)

def numErasures (e : ErasedWord n α) : ℕ :=
  (Finset.univ.filter (fun i => e i = none)).card
```

The key theorem:

```lean
theorem erasure_correction (C : Code n α) (d : ℕ)
    (h_dist : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → d ≤ hammingDist u v)
    (c : Codeword n α) (hc : c ∈ C)
    (e : ErasedWord n α) (h_cons : consistent c e)
    (h_era : numErasures e ≤ d - 1) :
    ∀ c' ∈ C, consistent c' e → c' = c
```

The proof in Lean formalizes the argument above: positions where $c$ and $c'$ differ must be erased (since unerased positions force agreement), so $d(c, c') \leq \text{numErasures}(e) \leq d-1 < d$.

**Erasure decoding examples:**

```lean
-- Repetition code [3,1,3]: sent 111, positions 0 and 2 erased → received ?1?
#eval decodeErasureEval repCode3
  (![none, some true, none] : Fin 3 → Option Bool)
-- Output: some (fun _ => true)  ✓

-- [7,4,3] code: sent 0000000, positions 3 and 5 erased → received 000?0?0
#eval decodeErasureEval hammingCode74List
  (![some false, some false, some false, none, some false, none, some false])
-- Output: some (fun _ => false)  ✓
```

**Errors vs. erasures — a summary:**

| Channel model | Receiver knows error locations? | Code can handle |
|---|---|---|
| Error channel | No | $\leq \lfloor (d-1)/2 \rfloor$ errors |
| Erasure channel | Yes | $\leq d-1$ erasures |

The erasure capacity is exactly twice as large — knowing the error locations is worth a factor of 2.

## 5. The Hamming Bound

### 5.1 The Ball Volume Formula

**Definition:** 
The **volume** of a Hamming ball of radius $t$ in $\alpha^n$ (with $\lvert\alpha\rvert = q$) is:

$$V(n, t, q) = \sum_{i=0}^{t} \binom{n}{i}(q-1)^i$$

**Why this formula?** A word $w$ satisfies $d(u, w) = i$ (exactly $i$ positions differ from $u$) iff:
* We choose which $i$ positions differ: $\binom{n}{i}$ ways
* For each differing position $j$, we choose a symbol $\neq u_j$: $q-1$ choices each

Total for exactly $i$ differences: $\binom{n}{i}(q-1)^i$.
Sum over $i = 0, 1, \ldots, t$ gives all words at distance $\leq t$ from $u$.

**Note:**
This formula is the same for any center $u$ — the Hamming metric is "translation-invariant" in the sense that all balls of the same radius have the same size.

```lean
def ballVol (n t q : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (t + 1), Nat.choose n i * (q - 1) ^ i

#eval ballVol 3 1 2  -- 4  = C(3,0) + C(3,1) = 1 + 3
#eval ballVol 7 1 2  -- 8  = C(7,0) + C(7,1) = 1 + 7
#eval ballVol 7 3 2  -- 64 = 1 + 7 + 21 + 35
```

### 5.2 The Hamming Bound

**Theorem (Hamming Bound / Sphere-Packing Bound):**

Let $C$ be an $(n, M, d)$-code over a $q$-ary alphabet with $d \geq 2t + 1$. Then:

$$M \cdot V(n, t, q) \leq q^n$$

Equivalently:

$$M \leq \frac{q^n}{\displaystyle\sum_{i=0}^{t}\binom{n}{i}(q-1)^i}$$

**Proof:**

1. The $M$ Hamming balls $B(c_1, t), B(c_2, t), \ldots, B(c_M, t)$ are pairwise disjoint (proved above).

2. Each ball has size $V(n, t, q)$ (the volume formula).

3. All balls are subsets of $\alpha^n$, which has $q^n$ elements.

4. Therefore:

$$M \cdot V(n, t, q) = \left|\bigcup_{c \in C} B(c, t)\right| \leq |\alpha^n| = q^n$$

The formalization in Lean captures the key logical steps:

```lean
theorem hamming_bound (C : Code n α) (t : ℕ)
    (h_dist : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → 2 * t + 1 ≤ hammingDist u v) :
    C.card * ballVol n t (Fintype.card α) ≤ (Fintype.card α) ^ n
```

### 5.3 Perfect Codes

A code achieving **equality** in the Hamming bound is called a **perfect code**. The Hamming balls around its codewords form a perfect tiling of $\alpha^n$ — no overlaps, no gaps.

**Examples of perfect codes:**
* The binary Hamming codes Ham$(r, 2)$ are perfect 1-error-correcting codes
* The binary $[23, 12, 7]$ Golay code is a perfect 3-error-correcting code
* The trivial codes: $\alpha^n$ itself (the "full" code, $t = 0$) and single-codeword codes

**Check: the triple repetition code is perfect.**

```lean
#eval (hammingBall (n := 3) (α := Bool) (fun _ => false) 1).card  -- 4
#eval (hammingBall (n := 3) (α := Bool) (fun _ => true)  1).card  -- 4
-- 2 codewords × 4 words per ball = 8 = 2^3  ✓
```

### 5.4 Why Perfect Codes Are Rare

The Hamming bound is a necessary condition for perfect codes — but it's a remarkable result that perfect binary codes have been completely classified:

**Theorem (Perfect Code Classification):** The only perfect binary codes are:
* Hamming codes Ham$(r, 2)$ for $r \geq 2$
* The $[23, 12, 7]$ Golay code
* Trivial (single-codeword or full-space) codes

This classification theorem is deep and non-trivial — a testament to the power of the constraints imposed by the Hamming bound.

## 6. The Singleton Bound

### 6.1 Statement

**Theorem (Singleton Bound, 1964):** For any $(n, M, d)$-code over a $q$-ary alphabet:

$$M \leq q^{n-d+1}$$

**Comparison with the Hamming Bound:** The Singleton bound is weaker for small $t$ but has a simpler proof, and it gives a tight bound for **MDS codes** (see below).

In Lean:

```lean
theorem singleton_bound (C : Code n α) (d : ℕ)
    (hd : 1 ≤ d) (hdn : d ≤ n)
    (h_minDist : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → hammingDist u v ≥ d) :
    C.card ≤ (Fintype.card α) ^ (n - d + 1)
```

### 6.2 Proof: The Puncturing Argument

The proof uses a beautiful **projection (puncturing) argument**.

**Setup:** Define the projection map that keeps only the first $n - d + 1$ coordinates:

$$f : \alpha^n \to \alpha^{n-d+1}, \quad f(c_1, c_2, \ldots, c_n) = (c_1, c_2, \ldots, c_{n-d+1})$$

```lean
def project (k : ℕ) (hk : k ≤ n) (c : Codeword n α) : Codeword k α :=
  fun i => c (Fin.castLE hk i)
```

**Key claim:** $f$ is **injective on** $C$ — distinct codewords project to distinct images.

**Proof of injectivity:** Suppose $f(u) = f(v)$ for distinct $u, v \in C$. Then $u$ and $v$ agree on the first $n - d + 1$ positions. So they can only disagree on the last $d - 1$ positions. Therefore:

$$d(u, v) \leq d - 1$$

But $d(u, v) \geq d$ (by the minimum distance assumption). **Contradiction.**

```lean
lemma project_ne_of_large_dist (d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n)
    (u v : Codeword n α) (h_dist : hammingDist u v ≥ d) (h_neq : u ≠ v) :
    project (n - d + 1) (by omega) u ≠ project (n - d + 1) (by omega) v
```

**Conclusion:** Since $f : C \to \alpha^{n-d+1}$ is injective and $\lvert\alpha^{n-d+1}\rvert = q^{n-d+1}$:

$$|C| \leq |\alpha^{n-d+1}| = q^{n-d+1}$$

The Lean proof uses `Finset.card_le_card_of_injOn`:

```lean
calc C.card
    ≤ (Finset.univ (α := Codeword (n - d + 1) α)).card := by
      apply Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) h_inj
  _ = (Fintype.card α) ^ (n - d + 1) := by
      simp [Codeword, Fintype.card_univ, Fintype.card_pi, Fintype.card_fin]
```

### 6.3 MDS Codes

A code achieving **equality** in the Singleton bound — $M = q^{n-d+1}$ — is called an **MDS code** (Maximum Distance Separable). These are the "best possible" codes in the sense of maximizing $M$ for given $n$ and $d$.

**Examples:**
* **Reed-Solomon codes** are MDS codes over large alphabets (a cornerstone of modern coding theory and used in CDs, DVDs, QR codes)
* The binary repetition code of length $n$ has $M = 2$, $d = n$, so $M = 2 = 2^{n - n + 1} = 2^1$ — it achieves equality! It is MDS.

**The MDS conjecture:** Over a field $\mathbb{F}_q$, the only MDS codes with $d \geq 3$ and $2 \leq M \leq q^{n-d+1}$ have $n \leq q + 1$ (with minor exceptions). This is a major open problem in coding theory, proved only for prime fields.

## 7. Comparing the Bounds

Here is a comparison of the two main bounds for binary codes ($q = 2$):

| Bound | Formula |
|-------|---------|
| **Hamming** | $M \leq 2^n \big/ \sum_{i=0}^{t} \binom{n}{i}$ |
| **Singleton** | $M \leq 2^{n-d+1}$ |

**Example:** For $n = 7$, $d = 3$ (so $t = 1$):
* **Hamming:** $M \leq 2^7 / (1 + 7) = 128 / 8 = 16$
* **Singleton:** $M \leq 2^{7-3+1} = 2^5 = 32$

The Hamming bound is tighter here. Indeed, the Hamming code Ham$(3, 2)$ achieves $M = 16$.

## 8. New Lean Techniques in This Lecture

Several proof techniques are introduced or emphasized in this lecture:

### 8.1 `Finset.card_le_card_of_injOn`

This lemma formalizes the argument "if $f : A \to B$ is injective on $A$, then $\lvert A\rvert \leq \lvert B \rvert$":

```lean
theorem Finset.card_le_card_of_injOn {s : Finset α} {t : Finset β}
    (f : α → β) (hf : ∀ x ∈ s, f x ∈ t) (h_inj : Set.InjOn f s) :
    s.card ≤ t.card
```

This is used in the proof of the Singleton bound.

### 8.2 `omega` and `linarith` for Arithmetic

The `omega` tactic handles linear arithmetic over natural numbers and integers. It is used extensively to close arithmetic goals of the form `a ≤ b` or `a = b`. For example:

```lean
have h_tri : hammingDist u v ≤ 2 * t
have h_ge : 2 * t + 1 ≤ hammingDist u v
omega  -- derives False automatically
```

### 8.3 `Finset.disjoint_left`

To prove two `Finset`s are disjoint, it suffices to show no element belongs to both:

```lean
rw [Finset.disjoint_left]
intro w hwu hwv
-- Now derive a contradiction from hwu and hwv
```

### 8.4 Working with `abbrev` and Type Aliases

We use `abbrev` (rather than `def`) for `Codeword` and `Code` so that Lean unfolds them eagerly during type-checking. This means that whenever Lean sees `Codeword n α`, it immediately knows it is `Fin n → α`, without needing an explicit `unfold` step.

Compare:
```lean
abbrev Codeword (n : ℕ) (α : Type*) := Fin n → α   -- transparent to Lean
def   CodeType  (n : ℕ) (α : Type*) := Fin n → α   -- opaque, requires unfold
```

### 8.5 `Fintype.card_pi`

The number of functions from a finite type $A$ to a finite type $B$ is $\lvert B \rvert^{\lvert A \rvert}$. In Lean:

```lean
Fintype.card_pi : Fintype.card (∀ i : α, β i) = ∏ i, Fintype.card (β i)
```

For `Codeword n α = Fin n → α`:
```lean
Fintype.card (Codeword n α) = (Fintype.card α) ^ n
```

This is used in both the Hamming and Singleton bound proofs to identify $\lvert\alpha^n\rvert = q^n$.

## 9. Homework Exercises

The following lemmas are left as homework (marked `sorry` in the demo):

### Exercise 1: Symmetry of Hamming Distance

Prove that `hammingDist'` (our pedagogical definition) is symmetric:

```lean
lemma hammingDist'_comm (u v : Codeword n α) :
    hammingDist' u v = hammingDist' v u
```

**Hint:** Show the Finsets `univ.filter (fun i => u i ≠ v i)` and `univ.filter (fun i => v i ≠ u i)` are equal. Use `Finset.filter_congr`.

### Exercise 2: Triangle Inequality

Prove the triangle inequality for `hammingDist'`:

```lean
lemma hammingDist'_triangle (u v w : Codeword n α) :
    hammingDist' u w ≤ hammingDist' u v + hammingDist' v w
```

**Hint:** If `u i ≠ w i`, then it cannot be the case that both `u i = v i` and `v i = w i`. So `{i | u i ≠ w i} ⊆ {i | u i ≠ v i} ∪ {i | v i ≠ w i}`. Use `Finset.card_le_card` and `Finset.card_union_le`.

### Exercise 3: Minimum Distance of the Repetition Code

Prove that the binary repetition code of length $n \geq 2$ has minimum distance $n$:

```lean
lemma repetitionCode_minDist (n : ℕ) (hn : n ≥ 2) :
    hasMinDist (repetitionCode n) n
```

**Hint:** The two codewords are `fun _ => false` and `fun _ => true`. Compute their Hamming distance explicitly.

### Exercise 4: Error Detection

Formalize that a code with minimum distance $d$ detects up to $d - 1$ errors:

```lean
lemma detects_dMinus1_errors (C : Code n α) (d : ℕ) (hd : 1 ≤ d)
    (h_minDist : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → hammingDist u v ≥ d)
    (c r : Codeword n α) (hc : c ∈ C)
    (h_errors : 1 ≤ hammingDist c r) (h_few : hammingDist c r ≤ d - 1) :
    r ∉ C
```

**Hint:** Suppose for contradiction that `r ∈ C`. Since `r ≠ c` (as `1 ≤ d(c,r)`), the minimum distance hypothesis gives `d(c,r) ≥ d`. But `d(c,r) ≤ d-1`. Contradiction via `omega`.

## 10. Summary

In this lecture, we:
* Defined codes, Hamming distance, and minimum distance in Lean
* Built example codes: repetition code and parity check code
* Proved that balls around codewords are disjoint when $d \geq 2t+1$
* Stated and partially proved the **Hamming Bound** $M \cdot V(n,t,q) \leq q^n$
* Proved the **Singleton Bound** $M \leq q^{n-d+1}$ via the projection argument

### Connections to Previous Lectures

* **Lecture 1–3:** Basic tactics, logical connectives, and Lean syntax remain the foundation
* **Lecture 4:** The style of defining combinatorial objects (like `hammingDist` analogous to `hammingWeight`, `Finset.filter`) and complexity parameters follows the same pattern as decision tree complexity
* **Lecture 5:** The `Finset.card_le_card_of_injOn` pattern mirrors the pigeonhole arguments used for graph colorings and walks

### Further Topics in Coding Theory

Coding theory is vast. From here, one could formalize:
* **Linear codes:** codes that form a linear subspace of $\mathbb{F}_q^n$, characterized by generator/parity-check matrices
* **The Gilbert-Varshamov bound:** a lower bound on code size showing good codes exist
* **Algebraic codes:** Reed-Solomon, BCH, and algebraic geometry codes
* **LDPC codes and iterative decoding:** modern codes approaching Shannon capacity
* **Connections to complexity:** PCPs and the Raz-Reingold-Wigderson theorem
* **Quantum codes:** CSS codes, stabilizer codes (a direction our research group is pursuing — see the `QuantumHamming.lean` and `QuantumSingleton.lean` files in the TCSlib repository)
