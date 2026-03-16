---
layout: lecture
title: "Lecture 8: Reducibility among NP-complete problems"
date: 2026-03-13
demo_url: https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fucb-lean-course-sp26%2Fucb-lean-course-sp26.github.io%2Frefs%2Fheads%2Fmain%2FLeanSource%2FDemos%2FLec8.lean
demo_sol_url: https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fucb-lean-course-sp26%2Fucb-lean-course-sp26.github.io%2Frefs%2Fheads%2Fmain%2FLeanSource%2FDemos%2FLec8sol.lean
---

* TOC
{:toc}

## 1. Overview & Background

In this lecture, we formalize reductions between NP-complete problems.
Specifically, we illustrate two reductions:
1. `Subset Sum` to `Partition`,
2. `Not-All-Equal-3-SAT` to `3-Coloring`.

### What We Will Cover

1. **Definitions of NP and reductions** and their Lean encodings
2. **Subset Sum → Partition:** the `partitionWeight` reduction, completeness, and soundness
3. **NAE-3SAT → 3-Coloring:** an inductive vertex type, an explicit edge relation, and a correctness proof by case analysis
4. **New Lean techniques:** `U ⊕ Bool` for universe augmentation, inductive types for heterogeneous vertex sets, `fin_cases` and `by_cases` for exhaustive case splits, and `Finset.sum_add_sum_compl`

### Brief Background on NP-completeness

A language $L \subseteq \\{0, 1\\}^{\*}$ is said to be in $\mathsf{NP}$ (non-deterministic polynomial
time) if there exists a (deterministic) polynomial time "verifier" algorithm $V$
and a function $p : \mathbb{N} \to \mathbb{N}$ with $p(n) = O(n^c)$ for some $c$ such that:

* *(Completeness)* If $x \in L$, there exists a "witness" $y$, with $\|y\| \le p(\|x\|)$, such that $V(x, y)$ accepts.
* *(Soundness)* If $x \notin L$, for all $y$ with $\|y\| \le p(\|x\|)$, $V(x, y)$ rejects.

### Reducibility among Problems

Given two languages $L_A$, $L_B$ $\subseteq \\{0, 1\\}^\*$,
a **polynomial time reduction** from $L_A$ to $L_B$ is a polynomial-time
computable function $R : \\{0, 1\\}^* \to \\{0, 1\\}^*$ such that for all
$x$, it holds that $x \in L_A \iff R(x) \in L_B$.

This equivalence is typically proved in two parts:
* **Completeness**: If $x \in L_A$, then $R(x) \in L_B$.
(A solution to the original problem implies a solution to the new problem.)

* **Soundness**: If $R(x) \in L_B$, then $x \in L_A$.
(A solution to the new problem implies a solution to the original problem.)

## 2. Subset Sum and Partition

### 2.1 Problem Definitions

The **Subset Sum** problem asks: given a weight function $w : U \to \mathbb{N}$
and a target integer $T$, does there exist a subset $S \subseteq U$ such that
the sum of weights of elements in $S$ is exactly $T$?

```lean
noncomputable def SubsetSum (w : U → ℕ) (T : ℕ) : Prop :=
  ∃ S : Finset U, (∑ a ∈ S, w a) = T
```

The **Partition** problem asks: given a weight function $w : U \to \mathbb{N}$,
does there exist a subset $S \subseteq U$ such that the sum of weights in $S$
equals the sum of weights in its complement $S^c$?

```lean
noncomputable def Partition (v : U → ℕ) : Prop :=
  ∃ S : Finset U, (∑ b ∈ S, v b) = (∑ b ∈ Sᶜ, v b)
```

Partition is a special case of Subset Sum where the target $T$ is exactly half
of the total weight of all elements.

### 2.2 The Reduction

Given a Subset Sum instance with weight $w : U \to \mathbb{N}$ and target $T$, we create
an instance of Partition as follows:
* Augment the universe with two new "dummy" elements: $U' = U \cup \{\top, \bot\}$.
* The new weight function $w' : U' \to \mathbb{N}$ agrees with $w$ on original elements,
  and assigns $w'(\top) = 2W - T$ and $w'(\bot) = W + T$, where $W = \sum_{x \in U} w(x)$.

In Lean, we represent the augmented universe as `U ⊕ Bool` — a disjoint union where
`Sum.inl a` represents original elements and `Sum.inr true` / `Sum.inr false` represent
the two dummy items $\top$ and $\bot$:

```lean
def partitionWeight (w : U → ℕ) (T : ℕ) : U ⊕ Bool → ℕ
  | Sum.inl a    => w a
  | Sum.inr true  => 2 * (∑ a, w a) - T    -- weight of ⊤
  | Sum.inr false => (∑ a, w a) + T         -- weight of ⊥
```

**Why `U ⊕ Bool`?** Using Lean's built-in sum type `U ⊕ Bool` lets us cleanly inject elements from `U` into the augmented universe with `Sum.inl`, while `Sum.inr true` and `Sum.inr false` name the two dummy elements without requiring any integer indexing or new inductive type.

**Note on natural number subtraction.** Because Lean's `ℕ` truncates subtraction at zero, the expression `2 * W - T` is only meaningful when `T ≤ W`. The theorems below all carry the hypothesis `(h : T ≤ ∑ a, w a)` for this reason — if `T > W` then Subset Sum is vacuously false anyway, since no subset of $U$ can have weight exceeding $W$.

### 2.3 Completeness

**Theorem.** If there exists $S \subseteq U$ with $\sum_{x \in S} w(x) = T$, then the
augmented weight function `partitionWeight w T` admits a partition.

**Proof.** Take $S' = \{\\, \mathtt{Sum.inl}\ a \mid a \in S\\,\} \cup \{\\,\mathtt{Sum.inr\ true}\\,\}$, i.e., the image of $S$ under `Sum.inl` together with the dummy element $\top$.

* **LHS sum:** $\sum_{b \in S'} w'(b) = \left(\sum_{a \in S} w(a)\right) + (2W - T) = T + (2W - T) = 2W$.
* **Total sum:** $\sum_{b : U \oplus \mathsf{Bool}} w'(b) = W + (2W - T) + (W + T) = 4W$.
* **RHS sum:** By `Finset.sum_add_sum_compl`, LHS + RHS = total, so RHS = $4W - 2W = 2W$.

```lean
theorem SubsetSumToPartitionCompleteness (w : U → ℕ) (T : ℕ) (h : T ≤ ∑ a, w a) :
    SubsetSum w T → Partition (partitionWeight w T) := by
  intro ⟨S, hS⟩
  let S' := S.image Sum.inl ∪ {Sum.inr true}
  refine ⟨S', ?_⟩
  have hDisj : Disjoint (S.image Sum.inl) ({Sum.inr true} : Finset (U ⊕ Bool)) := by simp
  have hSumLHS : ∑ b ∈ S', partitionWeight w T b = 2 * (∑ a, w a) := by
    rw [Finset.sum_union hDisj,
        Finset.sum_image (fun a _ b _ hab => Sum.inl.inj hab),
        Finset.sum_singleton]
    simp only [partitionWeight]; rw [hS]; omega
  have hTotalSum : ∑ b : U ⊕ Bool, partitionWeight w T b = 4 * (∑ a, w a) := by
    simp only [Fintype.sum_sum_type, Fintype.sum_bool, partitionWeight]; omega
  have hadd := Finset.sum_add_sum_compl S' (partitionWeight w T)
  rw [hTotalSum] at hadd; omega
```

Key lemmas used:
* `Finset.sum_union` — splits a sum over a disjoint union $A \cup B$ into $\sum_A + \sum_B$
* `Finset.sum_image` — collapses a sum over an injective image $f(S)$
* `Finset.sum_add_sum_compl` — the fundamental identity $\sum_{b \in S} f(b) + \sum_{b \in S^c} f(b) = \sum_b f(b)$

### 2.4 Soundness

**Theorem.** If `partitionWeight w T` admits a partition $S' \subseteq U'$, then there exists $S \subseteq U$ with $\sum_{x \in S} w(x) = T$.

**Proof sketch.** Any partition has each side summing to $2W$ (since the total is $4W$). We decompose the sum over $S'$ into contributions from the original elements and the two dummy items, then case-split on which dummies are in $S'$:

* **Both dummies** in $S'$: their combined weight is $(2W-T)+(W+T) = 3W > 2W$ — contradiction.
* **Neither dummy** in $S'$: the original elements contribute $\le W < 2W$ — contradiction.
* **Only $\top$ in $S'$**: $\sum_{a \in S_U} w(a) + (2W-T) = 2W$, so $\sum_{a \in S_U} w(a) = T$.
* **Only $\bot$ in $S'$**: $\sum_{a \in S_U} w(a) + (W+T) = 2W$, so $\sum_{a \in S_U} w(a) = W-T$, meaning the complement $U \setminus S_U$ has weight $T$.

In Lean, the case split on the dummy memberships is done with `by_cases`:

```lean
by_cases ht : Sum.inr true ∈ S
· by_cases hf : Sum.inr false ∈ S
  · -- both in S: omega gives contradiction
  · exact ⟨SU, by omega⟩         -- SU witnesses SubsetSum
· by_cases hf : Sum.inr false ∈ S
  · exact ⟨Finset.univ \ SU, by omega⟩   -- complement witnesses SubsetSum
  · -- neither in S: omega gives contradiction
```

The main work before the case split is to show that the sum over $S'$ decomposes as:

$$\sum_{b \in S'} w'(b) = \sum_{a \in S_U} w(a) + \mathbb{1}[\top \in S'] \cdot (2W - T) + \mathbb{1}[\bot \in S'] \cdot (W + T)$$

This is done by rewriting $S'$ as a union of its `inl`-part and `inr`-part, then applying `Finset.sum_union` and `Finset.sum_image` again.

### 2.5 Main Theorem

The completeness and soundness lemmas combine into a clean `Iff`:

```lean
theorem SubsetSumToPartitionReduction (w : U → ℕ) (T : ℕ) (h : T ≤ ∑ a, w a) :
    SubsetSum w T ↔ Partition (partitionWeight w T) :=
  Iff.intro
    (SubsetSumToPartitionCompleteness w T h)
    (SubsetSumToPartitionSoundness w T h)
```

## 3. NAE-3SAT and 3-Coloring

### 3.1 Problem Definitions

**Not-All-Equal Satisfiability (NAE-3SAT).** Given Boolean variables $x_1, \dots, x_n$ and clauses $C_1, \dots, C_m$, where each clause is a *triple* of variables, does there exist a Boolean assignment such that in every clause the three variables do not all receive the same value?

In Lean, a clause is a `structure` with three variable fields:

```lean
structure NAEclause (V : Type) where
  v0 : V
  v1 : V
  v2 : V

def SatisfiesClause {V : Type} (assign : V → Bool) (c : NAEclause V) : Bool :=
  assign c.v0 ≠ assign c.v1 || assign c.v0 ≠ assign c.v2 || assign c.v1 ≠ assign c.v2

abbrev NAESat3 (V : Type) := List (NAEclause V)

noncomputable def IsSatisfiable {V : Type} (f : NAESat3 V) : Prop :=
  ∃ (assign : V → Bool), SatisfiesNAE3 assign f = true
```

**3-Coloring.** Using Mathlib's `SimpleGraph` library, a graph `G` is 3-colorable if there exists a graph homomorphism from `G` to the complete graph on 3 vertices — equivalently, a function from vertices to `Fin 3` that assigns different colors to adjacent vertices:

```lean
def Is3Colorable {V' : Type} (G : SimpleGraph V') : Prop :=
  Nonempty (G.Coloring (Fin 3))
```

`SimpleGraph.Coloring` is Mathlib's bundled notion: a `G.Coloring α` is a function `V → α` that is a graph homomorphism to the complete graph on `α` (i.e., adjacent vertices receive different values).

### 3.2 The Reduction: Vertex Set

The key design challenge in any graph reduction is representing a heterogeneous set of vertices. We have three distinct *kinds* of vertices: one ground node, one node per variable, and three gadget nodes per clause. Rather than encoding them as integers, we use an **inductive type**:

```lean
inductive OutputVertex (V : Type)
  | groundNode                                  -- 1 ground vertex
  | varNode (v : V)                             -- 1 per variable
  | clauseNode (c : NAEclause V) (idx : Fin 3)  -- 3 per clause
```

This approach:
* Makes each constructor self-documenting
* Lets Lean's `match` expression exhaustively check all cases
* Avoids off-by-one errors that arise with integer-indexed vertex sets

### 3.3 The Reduction: Edge Relation

We define the edge predicate directly by pattern matching on vertex constructors:

```lean
def EdgeRelation {V : Type} (clauses : NAESat3 V) (u v : OutputVertex V) : Prop :=
  match u, v with
  | .groundNode, .varNode _         => True
  | .varNode _, .groundNode         => True
  | .varNode v, .clauseNode c i     =>
      (v = c.v0 ∧ i = 0) ∨ (v = c.v1 ∧ i = 1) ∨ (v = c.v2 ∧ i = 2)
  | .clauseNode c i, .varNode v     =>
      (v = c.v0 ∧ i = 0) ∨ (v = c.v1 ∧ i = 1) ∨ (v = c.v2 ∧ i = 2)
  | .clauseNode c1 i, .clauseNode c2 j =>
      c1 = c2 ∧ c1 ∈ clauses ∧ i ≠ j
  | _, _                            => False
```

The structure is:
1. Ground node connects to every variable node.
2. Variable $v$ connects to clause gadget node $c_{r,k}$ iff $v$ is the $k$-th variable of clause $c_r$.
3. The three gadget nodes within the same clause form a **triangle** — all pairs are connected.
4. All other pairs have no edge.

We then wrap `EdgeRelation` in a `SimpleGraph` by symmetrizing and enforcing irreflexivity:

```lean
def ReductionGraph {V : Type} (f : NAESat3 V) : SimpleGraph (OutputVertex V) where
  Adj u v := u ≠ v ∧ (EdgeRelation f u v ∨ EdgeRelation f v u)
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless  := ⟨fun _ h => h.1 rfl⟩
```

The visual structure for one clause $(x_1, x_2, x_3)$ is:

```none
        ⊥
        |
  +-----+-----+
  |     |     |
 x_1   x_2   x_3
  |     |     |
 c_1---c_2---c_3
  |           |
  +-----------+
```

### 3.4 The Reduction: Coloring Function

The completeness direction requires constructing an explicit 3-coloring from a NAE-3SAT assignment. The coloring rule is:

| Vertex kind | Color |
|---|---|
| `groundNode` | $0$ |
| `varNode v` | $1$ if `assign v = true`, else $2$ |
| `clauseNode c k` | determined by `clauseNodeColor (assign c.v0) (assign c.v1) (assign c.v2) k` |

For clause gadget nodes, the color must differ from the adjacent variable node and from the other two gadget nodes. Since not all three variables have the same value (NAE condition), exactly one of the six non-all-equal patterns holds. We encode the coloring with a lookup table:

```lean
private def clauseNodeColor (a b c : Bool) (k : Fin 3) : Fin 3 :=
  match a, b, c with
  | true,  true,  false => match k with | 0 => 0 | 1 => 2 | 2 => 1
  | true,  false, true  => match k with | 0 => 0 | 1 => 1 | 2 => 2
  | false, true,  true  => match k with | 0 => 1 | 1 => 0 | 2 => 2
  | true,  false, false => match k with | 0 => 2 | 1 => 0 | 2 => 1
  | false, true,  false => match k with | 0 => 0 | 1 => 2 | 2 => 1
  | false, false, true  => match k with | 0 => 0 | 1 => 1 | 2 => 2
  | _,     _,     _     => 0   -- all-equal: no clause-clause edges, any color works
```

The coloring of the full graph is then:

```lean
private def naeColoring {V : Type} (assign : V → Bool) : OutputVertex V → Fin 3
  | .groundNode    => 0
  | .varNode v     => if assign v then 1 else 2
  | .clauseNode c k => clauseNodeColor (assign c.v0) (assign c.v1) (assign c.v2) k
```

### 3.5 Completeness

**Theorem.** If the NAE-3SAT instance `f` is satisfiable, then `ReductionGraph f` is 3-colorable.

**Proof.** Use `naeColoring assign` as the witness. We must show that every adjacent pair gets different colors. The proof case-splits on the 6 possible edge types in `EdgeRelation`:

1. **Ground → Var:** `groundNode` gets color $0$; `varNode v` gets $1$ or $2$. Always distinct.
2. **Var → Clause:** After `rcases` pins down which variable index ($0$, $1$, or $2$) the edge uses, a `cases` on all 8 combinations of `assign c.v0`, `assign c.v1`, `assign c.v2` closes each sub-goal by `simp [clauseNodeColor]`.
3. **Clause → Clause (triangle):** Both clause nodes belong to the same clause $c_r$. The hypothesis `hsat : SatisfiesNAE3 assign f = true` gives `SatisfiesClause assign c_r = true`. Then `fin_cases i <;> fin_cases j` generates all $3 \times 3$ combinations of indices; the diagonal (`i = j`) is ruled out by `hij`; the off-diagonal all-false/all-true cases are ruled out by `hNAE`; the remaining cases are closed by `simp_all [clauseNodeColor, SatisfiesClause]`.

The key tactic combination for the hardest case:

```lean
fin_cases i <;> fin_cases j <;>
  cases h0 : assign c1.v0 <;> cases h1 : assign c1.v1 <;> cases h2 : assign c1.v2 <;>
  simp_all [clauseNodeColor, SatisfiesClause]
```

This generates $9 \times 8 = 72$ sub-goals (3 choices for `i`, 3 for `j`, 2 for each of 3 variables), all of which `simp_all` dispatches automatically.

### 3.6 Soundness

**Theorem.** If `ReductionGraph f` is 3-colorable, then `f` is satisfiable.

**Proof.** Given a 3-coloring `col`, define:

```lean
let cTrue : Fin 3 := col .groundNode + 1
let assign v := decide (col (.varNode v) = cTrue)
```

The "true color" `cTrue` is defined as `groundColor + 1` in `Fin 3`, which is always different from the ground color. Variables are assigned `true` iff their node has the true color.

We must show every clause is NAE-satisfied. By contradiction: suppose clause $c$ is *not* NAE-satisfied, meaning all three variables get the same assignment value.

* **All true:** all three `varNode` colors equal `cTrue`.
* **All false:** each `varNode` is $\ne$ `cTrue` and $\ne$ `groundColor` (by the ground-variable edges). Since colors are in `Fin 3`, there is exactly one remaining value, so all three `varNode` colors are equal.

In both cases, the three `clauseNode c 0`, `clauseNode c 1`, `clauseNode c 2` are:
* Pairwise distinct (triangle edges)
* Each different from `varNode c.v0` (variable-clause edges)

But three pairwise-distinct elements of `Fin 3` cover all three values, so one of them must equal `col (varNode c.v0)` — contradiction. In Lean this is closed by `omega` after extracting all the `Fin 3` value inequalities:

```lean
have ne01 ... have ne02 ... have ne12 ...
have nex0 ... have nex1 ... have nex2 ...
omega
```

### 3.7 Main Theorem

```lean
theorem NAEtoColorReduction {V : Type} (f : NAESat3 V) :
    IsSatisfiable f ↔ Is3Colorable (ReductionGraph f) :=
  Iff.intro (NAEtoColorCompleteness f) (NAEtoColorSoundness f)
```

## 4. Proof Techniques Summary

### 4.1 `U ⊕ Bool` for Universe Augmentation

When a reduction adds a fixed small number of new elements to an existing universe, the cleanest Lean encoding is the **sum type** `U ⊕ Bool`:

```lean
-- Original elements: Sum.inl a  (for a : U)
-- First dummy:       Sum.inr true
-- Second dummy:      Sum.inr false
```

Pattern matching on `Sum.inl` vs `Sum.inr` is exhaustive and compiles cleanly to Lean's equation compiler. Lemmas like `Finset.sum_image` require injectivity of the injection function, which holds trivially for `Sum.inl`.

### 4.2 Inductive Types for Heterogeneous Vertex Sets

When vertices are of fundamentally different *kinds*, an **inductive type** is more expressive than a numeric encoding:

```lean
inductive OutputVertex (V : Type)
  | groundNode
  | varNode     (v : V)
  | clauseNode  (c : NAEclause V) (idx : Fin 3)
```

Benefits:
* Lean's `match` exhaustively covers all constructors — you cannot forget a case.
* Each constructor carries exactly the data it needs (e.g., `clauseNode` carries the clause and the index within it).
* Injectivity lemmas (`Sum.inl.inj`, etc.) or `simp` attributes handle equalities automatically.

### 4.3 `Finset.sum_add_sum_compl`

A key identity for partition-style arguments:

```lean
Finset.sum_add_sum_compl : ∀ (S : Finset α) (f : α → β),
    (∑ x ∈ S, f x) + (∑ x ∈ Sᶜ, f x) = ∑ x, f x
```

This is the go-to lemma when you know the total and one side; `omega` recovers the other side.

### 4.4 `by_cases` for Membership Splits

When the proof hinges on whether specific elements are in a finset, `by_cases` produces clean sub-goals:

```lean
by_cases ht : Sum.inr true ∈ S
· by_cases hf : Sum.inr false ∈ S
  · -- both in S
  · -- only ⊤ in S
· by_cases hf : Sum.inr false ∈ S
  · -- only ⊥ in S
  · -- neither in S
```

Each branch is a simple `omega` or a direct `⟨witness, proof⟩`.

### 4.5 `fin_cases` for Exhaustive Index Splits

`fin_cases i` replaces a variable `i : Fin n` with all `n` concrete values. Combined with `cases` on boolean variables, it turns an open-ended goal into finitely many fully concrete sub-goals:

```lean
fin_cases i <;> fin_cases j <;>
  cases assign c.v0 <;> cases assign c.v1 <;> cases assign c.v2 <;>
  simp_all [clauseNodeColor, SatisfiesClause]
```

This is a powerful "decision procedure by enumeration" that works whenever the types involved are small and finite.

### 4.6 Pigeonhole by `omega`

When three values in `Fin 3` must be pairwise distinct and each must avoid one fixed value, there are only $3! = 6$ possible arrangements — and all of them produce a contradiction. Rather than enumerating cases, we extract all `Fin.val` inequalities and let `omega` find the contradiction purely by arithmetic:

```lean
have cn0 := (col (.clauseNode c 0)).isLt    -- < 3
have ne01 : val(c0) ≠ val(c1) := ...
have nex0 : val(c0) ≠ val(varNode) := ...
-- ... (9 total constraints)
omega
```

## 5. Exercises

### Exercise 1: NAE-3SAT example

The file defines a small example:

```lean
def nae_sat_eg : NAESat3 (Fin 5) := [⟨0, 1, 2⟩, ⟨0, 1, 3⟩, ⟨0, 2, 4⟩]
def assign_eg := ![true, true, false, false, false]
```

Verify by `#eval` that `assign_eg` satisfies all three clauses, then prove the satisfiability statement:

```lean
example : IsSatisfiable nae_sat_eg := ⟨assign_eg, rfl⟩
```

Now find a *different* satisfying assignment (one that is not just the complement of `assign_eg`) and prove it works.

### Exercise 2: Partition implies Subset Sum

The main theorem `SubsetSumToPartitionReduction` requires `h : T ≤ ∑ a, w a`. Show that without this hypothesis the implication $\mathsf{SubsetSum}(w, T) \to \mathsf{Partition}(\mathsf{partitionWeight}\ w\ T)$ can fail by constructing a counterexample in Lean (use `decide` or `native_decide` on a small finite type).

## 6. Summary

In this lecture, we:

* Encoded **NP-complete problems** as `Prop`-valued predicates over `Finset`s and `List`s
* Formalized the **Subset Sum → Partition** reduction using `U ⊕ Bool` to augment the universe, and proved both directions of the equivalence using `Finset.sum_add_sum_compl`, `by_cases`, and `omega`
* Formalized the **NAE-3SAT → 3-Coloring** reduction using an inductive `OutputVertex` type, a pattern-matched `EdgeRelation`, and Mathlib's `SimpleGraph.Coloring`
* Used `fin_cases` combined with boolean case splits for exhaustive verification of the coloring constraints
* Used `omega` as a pigeonhole-in-`Fin 3` argument to close the soundness proof

### Design Principles

| Challenge | Technique |
|---|---|
| Augmenting a universe with $k$ elements | `U ⊕ Bool` / `U ⊕ Fin k` sum types |
| Heterogeneous vertex kinds | Inductive type per vertex kind |
| Partition/complement sums | `Finset.sum_add_sum_compl` |
| Boolean membership case splits | `by_cases` |
| Exhaustive finite enumeration | `fin_cases` + `cases` + `simp_all` |
| Pigeonhole in `Fin n` | Collect `.isLt` and `ne` facts, close with `omega` |

### Connections to Previous Lectures

* **Lectures 1–3:** `omega`, `simp`, `rcases`, and `by_cases` are used throughout
* **Lecture 5:** `Finset`-based arguments — sums, images, and complements — appear again
* **Lectures 4 & 6:** Graph colorings from Mathlib's `SimpleGraph` library reappear; the coloring reduction makes the combinatorial connection between logic and graph theory explicit

### Further Directions

* **3-SAT → 3-Coloring:** The classic direct reduction from 3-SAT, using a different gadget structure
* **Independent Set → Clique → Vertex Cover:** Simple complement-based reductions, easy to formalize with `SimpleGraph.compl`
* **Subset Sum → Knapsack:** Extend the `U ⊕ Bool` trick to multi-dimensional weight vectors
* **NP-hardness via Cook-Levin:** A Lean formalization of the Cook-Levin theorem (any NP language reduces to SAT) is an open challenge in formal methods
