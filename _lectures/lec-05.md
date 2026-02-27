---
layout: lecture
title: "Lecture 5: Introduction to Graphs in Lean"
date: 2026-02-20
# slides_url: https://docs.google.com/presentation/d/14QE7sfBIHN0sSnqdKcmph8CQRX6yQAMmiFrV-OsVL-M/edit?usp=sharing
demo_url: https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fucb-lean-course-sp26%2Fucb-lean-course-sp26.github.io%2Frefs%2Fheads%2Fmain%2FLeanSource%2FDemos%2FLec5.lean
demo_sol_url: https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2Fucb-lean-course-sp26%2Fucb-lean-course-sp26.github.io%2Frefs%2Fheads%2Fmain%2FLeanSource%2FDemos%2FLec5sol.lean
---

* TOC
{:toc}

## 1. Introduction

In this lecture, we introduce **graph theory** in Lean 4. Graphs are fundamental structures in theoretical computer science, appearing in algorithms, complexity theory, network analysis, and combinatorics.

We will:
* Define simple undirected graphs as structures with adjacency relations
* Prove a basic graph coloring theorem
* Define walks on graphs and prove properties about walk length

This lecture demonstrates how to formalize discrete mathematical structures in Lean and reason about their properties using tactics we've learned in previous lectures.

## 2. Defining Graphs in Lean

### 2.1 Basic Graph Structure

A **simple undirected loopless graph** consists of:
* A set of vertices `V`
* An adjacency relation `adj : V → V → Prop`
* **Symmetry:** if `u` is adjacent to `v`, then `v` is adjacent to `u`
* **Looplessness:** no vertex is adjacent to itself

We formalize this as a structure in Lean:

```lean
structure MyGraph (V : Type u) where
  adj : V → V → Prop
  symm : Symmetric adj
  loopless : Irreflexive adj
```

Here:
* `Symmetric adj` means `∀ x y, adj x y → adj y x`
* `Irreflexive adj` means `∀ x, ¬adj x x`

**Remark on Graph Representation:**
This is a **relational** representation of graphs, where adjacency is a logical proposition. This is different from:
* **Adjacency matrix** representation (common in algorithms)
* **Adjacency list** representation (common in programming)

The relational approach is natural for theorem proving because we can directly use logical reasoning about the adjacency relation. The symmetry and looplessness properties are **built into the structure**, so we never need to reprove them—they're guaranteed by construction.

### 2.2 Basic Graph Operations

For a graph `G : MyGraph V`, we define:

**Neighbors** of a vertex:
```lean
def neighbors (v : V) : Finset V := Finset.univ.filter (G.adj v)
```

**Degree** of a vertex (number of neighbors):
```lean
def degree (v : V) : ℕ := (G.neighbors v).card
```

### 2.3 Decidability

To work with finite computations on graphs (like filtering neighbors), we need the adjacency relation to be decidable:

```lean
variable {G : MyGraph V} [DecidableRel G.adj]
```

This allows Lean to determine computationally whether two vertices are adjacent.

## 3. Graph Coloring

### 3.1 Proper Coloring

A **proper coloring** of a graph assigns colors to vertices such that adjacent vertices receive different colors.

```lean
def ProperOn (S : Finset V) (k : ℕ) (c : V → Fin k) : Prop :=
  ∀ {x y}, x ∈ S → y ∈ S → G.adj x y → c x ≠ c y
```

Here:
* `S` is a set of vertices we want to color
* `k` is the number of available colors
* `c : V → Fin k` assigns each vertex a color from `{0, 1, ..., k-1}`
* The coloring is proper on `S` if no two adjacent vertices in `S` have the same color

### 3.2 Key Lemma: Finding an Available Color

**Lemma:** If a vertex `v` has degree at most `D`, then among `D+1` colors, at least one color is not used by any neighbor of `v`.

```lean
lemma exists_color_not_in_neighbors (D : ℕ) (v : V) (c : V → Fin (D + 1))
    (hdeg : G.degree v ≤ D) :
  ∃ col : Fin (D + 1), ∀ w ∈ G.neighbors v, col ≠ c w
```

**What this lemma says:** If a vertex has at most D neighbors, and we're trying to color it with D+1 colors, then at least one color is "safe" (not used by any neighbor).

**Proof Idea:**
1. Let `forbidden` be the set of colors used by neighbors of `v`
2. Since `v` has at most `D` neighbors, `|forbidden| ≤ D`
3. Since we have `D+1` colors total, at least one color is not forbidden
4. This color can be safely assigned to `v`

The proof uses the pigeonhole principle via `Finset.exists_mem_notMem_of_card_lt_card`.

**Key proof steps from the demo file:**

```lean
classical  -- Enable classical reasoning
let forbidden : Finset (Fin (D+1)) := (G.neighbors v).image c

have hforb : forbidden.card ≤ D := by
  exact (Finset.card_image_le).trans hdeg

have hlt : forbidden.card < (Finset.univ : Finset (Fin (D+1))).card := by
  simpa using (Nat.lt_succ_of_le hforb)

rcases Finset.exists_mem_notMem_of_card_lt_card hlt with ⟨col, hcolU, hcolNot⟩
```

**New tactics and techniques:**

* **`classical`**: Enables classical reasoning. This allows us to treat all propositions as decidable, which is needed for computational operations on sets that may not be constructively decidable. Without this, Lean wouldn't be able to compute the image of a function over a finite set in general.

* **`rcases ... with ⟨x, y, z⟩`**: A more powerful version of `cases` that allows **destructuring**. It simultaneously:
  - Performs case analysis
  - Extracts components from existential statements
  - Names the resulting hypotheses

  In this case, `Finset.exists_mem_notMem_of_card_lt_card` returns `∃ x, x ∈ univ ∧ x ∉ forbidden`, and `rcases` automatically gives us the witness `col` and the two proofs `hcolU` and `hcolNot`.

* **`simpa`**: Short for "simplify and apply". It simplifies the goal using `simp` and then tries to close it with `assumption` or `rfl`. Here it's used to simplify `forbidden.card < D + 1` using the fact that `Fintype.card (Fin (D+1)) = D + 1`.

### 3.3 Extending a Partial Coloring

**Lemma:** Given a proper coloring of `S \ {v}`, we can extend it to a proper coloring of `S`.

```lean
lemma extend_proper (D : ℕ) (S : Finset V) (v : V) (hv : v ∈ S)
    (hdeg : ∀ w, G.degree w ≤ D)
    (c : V → Fin (D + 1)) (hc : G.ProperOn (S.erase v) (D + 1) c) :
    ∃ c' : V → Fin (D + 1), G.ProperOn S (D + 1) c'
```

**What this lemma says:** If we can properly color all vertices in `S` except `v`, then we can find a proper coloring of all of `S` (including `v`).

**Proof Strategy:**
1. Use the previous lemma to find a safe color `new_col` for `v`
2. Define `c' := Function.update c v new_col` (same as `c` everywhere except at `v`)
3. Verify that `c'` is proper on all of `S` by case analysis:
   - If edge is `v ~ y`: `new_col ≠ c y` by construction (from the previous lemma)
   - If edge is `x ~ y` with both different from `v`: use the old coloring property

**The key technique: `Function.update`**

`Function.update c v new_col` creates a new function that:
* Returns `new_col` when applied to `v`
* Returns `c x` when applied to any other `x ≠ v`

This is formalized with two lemmas:
* `Function.update_self`: `(Function.update c v new_col) v = new_col`
* `Function.update_of_ne`: If `x ≠ v` then `(Function.update c v new_col) x = c x`

**Proof structure with nested `by_cases`:**

The proof performs **double case analysis** on whether the endpoints of an edge equal `v`:

```lean
by_cases hx : x = v
· -- Case 1: x = v
  by_cases hy : y = x
  · -- Case 1a: y = x (impossible - would be a loop)
    exact (G.loopless y hxy).elim
  · -- Case 1b: y ≠ x (so the edge is v ~ y)
    -- Use that new_col is safe for neighbors of v
· -- Case 2: x ≠ v
  by_cases hy : y = v
  · -- Case 2a: y = v (so the edge is x ~ v)
    -- Use symmetry of adjacency and that new_col is safe
  · -- Case 2b: both x ≠ v and y ≠ v
    -- Use the old coloring property
```

This systematic case analysis ensures we handle all possible edges correctly.

### 3.4 Main Coloring Theorem

**Theorem:** Any graph with maximum degree `D` is `(D+1)`-colorable.

```lean
theorem colorable_of_degree_le (D : ℕ) (hdeg : ∀ v, G.degree v ≤ D) (S : Finset V) :
    ∃ c : V → Fin (D + 1), G.ProperOn S (D + 1) c
```

**Proof by Induction on `S`:**

We use **structural induction on finite sets** via `Finset.induction_on`:

* **Base case (`S = ∅`):** The empty coloring works trivially—there are no vertices to color, so any coloring function satisfies the property vacuously.

* **Inductive step (`S = insert a s`):**
  1. **Induction Hypothesis:** By the inductive hypothesis, there exists a proper coloring `c` of `s` (the smaller set without `a`)
  2. **Key Observation:** Note that `(insert a s).erase a = s`. This needs to be proved using extensionality:
     ```lean
     have hErase : (insert a s).erase a = s := by
       ext x
       by_cases hx : x = a
       · simp [hx, ha]  -- if x = a, then x ∉ erase and x ∉ s (since a ∉ s)
       · simp [Finset.mem_erase, hx]  -- if x ≠ a, then x ∈ erase ↔ x ∈ insert ↔ x ∈ s
     ```
  3. **Extension:** Apply `extend_proper` to extend the coloring `c` from `s` to `insert a s`

**Why this works:** The theorem combines the greedy coloring algorithm with an inductive proof:
* Start with an empty graph (trivially colorable)
* Add vertices one at a time
* For each new vertex, there's always a safe color available (by the pigeonhole lemma)
* The resulting coloring is guaranteed to be proper

**Finset.induction_on pattern:**

This is a common pattern for proving properties about finite sets:

```lean
induction S using Finset.induction_on with
| empty =>
    -- Prove for the empty set
| @insert a s ha ih =>
    -- a : V (the new element)
    -- s : Finset V (the smaller set)
    -- ha : a ∉ s (a is not already in s)
    -- ih : the property holds for s
    -- Goal: prove the property for (insert a s)
```

**Remarks:**
* This is a constructive proof—it not only shows a coloring exists but provides an algorithm to find one
* This result is known as Brooks' theorem when restricted to connected graphs
* The proof technique (greedy coloring) is fundamental in graph algorithms

## 4. Walks in Graphs

### 4.1 Definition of a Walk

A **walk** from vertex `u` to vertex `v` is a sequence of edges connecting them.

We define walks inductively:

```lean
inductive Walk : V → V → Type u
  | nil  {u : V} : Walk u u
  | cons {u v w : V} (h : G.adj u v) (p : Walk v w) : Walk u w
```

* `nil` represents a walk of length 0 from a vertex to itself
* `cons h p` prepends an edge from `u` to `v` (given by adjacency proof `h`) to a walk `p` from `v` to `w`

**Important: Walks are a dependent type!**

Notice that `Walk : V → V → Type u` takes **two vertex parameters**. This means:
* `Walk u v` is a *different type* from `Walk u w` when `v ≠ w`
* The type itself encodes the endpoints of the walk
* A term of type `Walk u v` is *guaranteed* to be a walk from `u` to `v`

This is **dependent typing** in action: the type depends on values (`u` and `v`). This prevents us from accidentally using a walk with the wrong endpoints.

**Comparison with other representations:**

In a programming language without dependent types, you might represent a walk as `List (V × V)` (a list of edges) and separately track the endpoints. But then you need to:
* Check at runtime that consecutive edges connect properly
* Verify that the walk actually starts at `u` and ends at `v`

In Lean, these properties are guaranteed by the **type** itself—any term of type `Walk u v` is automatically well-formed.

### 4.2 Implicit Graph Parameters and `(G := G)` Syntax

You may notice that the walk definitions are written as:

```lean
inductive Walk : V → V → Type u
  | nil  {u : V} : Walk u u
  | cons {u v w : V} (h : G.adj u v) (p : Walk v w) : Walk u w
```

but later usage writes `Walk (G := G) u v`. Here is what is going on.

**`Walk` secretly takes `G` as an argument.**

Even though the source line only says `Walk : V → V → Type u`, Lean elaborates this to something like:

```lean
MyGraph.Walk (G : MyGraph V) : V → V → Type u
```

The graph `G` is pulled in as a parameter from the surrounding `variable (G : MyGraph V)` declaration. So the actual type of `Walk` is roughly:

```lean
Walk : MyGraph V → V → V → Type u
```

**Why write `(G := G)` explicitly?**

Lean often can infer `G` from context, but in type signatures of new definitions there may be no earlier argument from which to infer it. For example:

```lean
def length : {u v : V} → Walk (G := G) u v → Nat
```

If you wrote `Walk u v` here, Lean would complain because `Walk` needs a graph argument and there is nothing in scope to infer it from.

**What does `(G := G)` mean syntactically?**

It is **named argument syntax**: the first `G` is the name of the parameter in the definition, and the second `G` is the local variable you want to pass. So `Walk (G := G) u v` means "use the current graph `G` for the `G` parameter of `Walk`."

This is the same pattern as:

```lean
#check @id (α := Nat) 3
```

**Can we avoid writing it so much?**

Two common approaches:

* Make `G` explicit in the definition of `Walk`: `inductive Walk (G : MyGraph V) : V → V → Type u`. Then you write `Walk G u v` everywhere naturally.
* Keep it implicit and only write `(G := G)` when Lean cannot infer it from surrounding arguments. Inside a namespace with `variable {G}`, many definitions can omit it; in standalone type signatures it is often required.

Being explicit as shown in the demo avoids inference failures and makes it clear that all operations refer to the same graph.

### 4.3 Walk Length

The **length** of a walk is its number of edges:

```lean
def length : {u v : V} → Walk (G := G) u v → Nat
  | _, _, nil        => 0
  | _, _, cons _ p   => Nat.succ p.length
```

### 4.4 Walk Operations

**Appending walks:**

```lean
def append : {u v w : V} →
    Walk (G := G) u v → Walk (G := G) v w → Walk (G := G) u w
  | _, _, _, nil,        p2 => p2
  | _, _, _, cons h p1,  p2 => cons h (append p1 p2)
```

**Length of concatenated walks:**

```lean
@[simp] theorem length_append {u v w : V}
    (p1 : Walk (G := G) u v) (p2 : Walk (G := G) v w) :
    (append p1 p2).length = p1.length + p2.length
```

This is proved by induction on `p1`.

### 4.5 Converting Walks to Vertex Lists

A walk can be represented as a list of vertices it visits:

```lean
def toList : {u v : V} → Walk (G := G) u v → List V
  | u, _, nil        => [u]
  | u, _, cons _ p   => u :: p.toList
```

**Key property:** A walk of length `L` visits exactly `L+1` vertices:

```lean
@[simp] theorem length_toList {u v : V} (p : Walk (G := G) u v) :
    p.toList.length = p.length + 1
```

### 4.6 Shortening Walks with Duplicate Vertices

**Splicing Lemma:** If a walk's vertex list contains a duplicate, we can construct a strictly shorter walk with the same endpoints.

```lean
lemma exists_shorter_walk_of_not_nodup {u v : V} (p : Walk (G := G) u v) :
    ¬ p.toList.Nodup → ∃ (p' : Walk (G := G) u v), p'.length < p.length
```

**What this lemma says:** If a walk visits some vertex twice, we can "cut out" the loop between the two visits to get a shorter walk.

**Intuition:**

Suppose we have a walk `u → a → b → c → b → d → v`. The vertex `b` appears twice. We can shortcut the walk by going directly from the first `b` to where we are after the second `b`:
* Original: `u → a → b → c → b → d → v` (6 edges)
* Shortened: `u → a → b → d → v` (4 edges)

**Proof Strategy:**

If the vertex list `u :: tail` is not duplicate-free, then either:

1. **Case 1:** `u` appears again in `tail`
   - Use `dropTo u` to skip the prefix until the second occurrence of `u`
   - This creates a cycle-free walk from `u` to the destination
   - The new walk is strictly shorter because we removed the loop

2. **Case 2:** `tail` itself has duplicates (but `u` doesn't repeat)
   - By induction on the walk structure, we can shorten the `tail` walk
   - Prepend the first edge to get a shorter walk from `u` to `v`

**The `dropTo` operation:**

This is a sophisticated operation that uses dependent pattern matching:

```lean
def dropTo {u v : V} (p : Walk (G := G) u v) (x : V) (hx : x ∈ p.toList) :
    Walk (G := G) x v
```

**What `dropTo` does:** Given a walk `p : Walk u v` and a vertex `x` that appears in the walk, `dropTo p x hx` returns a walk from `x` to `v` by "dropping" the prefix of `p` before the first occurrence of `x`.

**The challenge:** The return type `Walk x v` depends on the *value* `x`, which is only known at runtime. This requires using `cast` to convince Lean that type equalities hold.

**Example from the code:**

```lean
| nil =>
    have h : x = u := by simpa [toList] using hx
    cast (by rw [h]) nil
```

In the `nil` case:
* We have a walk `nil : Walk u u` (just the vertex `u`)
* We know `x ∈ [u]`, so `x = u`
* We need to return `Walk x u`
* But we have `nil : Walk u u`
* Using `cast`, we rewrite the type using `h : x = u` to get `Walk x u`

**Why `cast` is needed:**

Lean's type checker is very strict. Even if we *prove* that `x = u`, the types `Walk x u` and `Walk u u` are still considered different until we explicitly apply the equality. The `cast` function takes a proof of type equality and converts a term of one type to the other.

**Proving `length_dropTo_le`:**

```lean
theorem length_dropTo_le {u v : V} (p : Walk (G := G) u v) (x : V) (hx : x ∈ p.toList) :
    (p.dropTo x hx).length ≤ p.length
```

This is left as homework. The key ideas:
* Use induction on the walk `p`
* Case split on whether `x = u` (the starting vertex)
* If `x = u`, we drop nothing, so `dropTo p x hx = p` (after cast)
* If `x ≠ u`, then `x` must be in the tail, and we recurse
* Use `le_trans` to combine inequalities from the inductive hypothesis

### 4.7 Main Theorem: Short Walk Existence

**Theorem:** For any walk from `u` to `v`, there exists a walk from `u` to `v` with length strictly less than the number of vertices.

```lean
theorem exists_short_walk {u v : V} (p_orig : Walk (G := G) u v) :
    ∃ (p : Walk (G := G) u v), p.length < Fintype.card V
```

**What this theorem says:** No matter how long a walk is, we can always find a shorter walk between the same endpoints that visits fewer than `|V|` edges. This is a fundamental property: to get from `u` to `v`, you never need to take more than `|V|-1` steps.

**Intuition:**

If a walk has length ≥ `|V|`, then it visits `|V|+1` or more vertices (since a walk of length `n` visits `n+1` vertices). But there are only `|V|` vertices in the graph! By the **pigeonhole principle**, some vertex must be visited at least twice. We can then remove the loop between the two visits to get a shorter walk.

**Proof by Strong Induction on Walk Length:**

This proof uses a **strong induction pattern** that's less common than simple induction. Here's the structure:

```lean
let P : ℕ → Prop :=
  fun n =>
    ∀ {u v : V} (p : Walk (G := G) u v), p.length = n →
      ∃ p' : Walk (G := G) u v, p'.length < Fintype.card V

have hP : ∀ n, P n := by
  intro n0
  refine Nat.strong_induction_on n0 ?_
  intro n ih
  -- ih : ∀ m < n, P m
  -- Goal: P n
```

**Breaking this down:**

1. **Define a predicate `P n`:** Instead of directly proving the theorem, we define a property `P n` that says: "for any walk of length `n`, there exists a short walk with the same endpoints"

2. **Prove `∀ n, P n` by strong induction:** Strong induction gives us:
   * **Induction hypothesis:** For all `m < n`, we already know `P m` holds
   * **Goal:** Prove `P n`

   This is stronger than regular induction because we can use *any* smaller case, not just `n-1`.

3. **Apply to the original walk:** Once we have `∀ n, P n`, we apply it to `p_orig.length` to get the result.

**The proof of `P n`:**

For a walk `p` of length `n`, we have two cases:

**Case 1: `p.length < |V|`**
```lean
by_cases h_small : p.length < Fintype.card V
· exact ⟨p, h_small⟩
```
The walk is already short enough—we're done!

**Case 2: `p.length ≥ |V|`**

Now the interesting part:

```lean
have h_not_nodup : ¬ p.toList.Nodup := by
  intro h_nodup
  -- If p.toList has no duplicates...
  have h1 : p.toList.length ≤ Fintype.card V :=
    nodup_length_le_card h_nodup
  -- Then it has at most |V| vertices
  have h2 : p.length + 1 ≤ Fintype.card V := by
    simpa [Walk.length_toList] using h1
  -- But p.length + 1 is the walk length, contradiction!
  have : p.length < Fintype.card V :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h2
  exact h_small this
```

This is a **proof by contradiction**:
* Assume `p.toList` has no duplicates
* Then it has at most `|V|` elements (by pigeonhole)
* But `p.length + 1 = p.toList.length` (a walk of length `n` visits `n+1` vertices)
* So `p.length < |V|`, contradicting our case assumption

Therefore, `p.toList` must have duplicates!

```lean
obtain ⟨p_shorter, h_shorter_len⟩ :=
  exists_shorter_walk_of_not_nodup p h_not_nodup

have hmn : p_shorter.length < n := by
  simpa [hp_len] using h_shorter_len

exact ih p_shorter.length hmn p_shorter rfl
```

* Use the splicing lemma to get a strictly shorter walk `p_shorter`
* Since `p_shorter.length < n`, we can apply the **strong induction hypothesis** `ih`
* The induction hypothesis gives us a walk of length `< |V|`

**Why strong induction is necessary:**

When we shorten the walk, we might not reduce the length by exactly 1—we might reduce it by more (if we remove a large loop). Regular induction only lets us assume the property for `n-1`, but strong induction lets us use it for *any* `m < n`, which is exactly what we need here!

**The crucial supporting lemma:**

```lean
theorem nodup_length_le_card {l : List V} (hl : l.Nodup) :
    l.length ≤ Fintype.card V
```

This is the pigeonhole principle: a duplicate-free list of vertices can contain at most `|V|` elements. This is left as homework.

## 5. Homework Exercises

The following lemmas are left as homework exercises (marked with `sorry` in the demo):

### Exercise 1: Symmetry of Proper Coloring

Prove that a proper coloring is symmetric in its two vertex arguments. That is, if the coloring is proper and two adjacent vertices `x` and `y` are in `S`, then not only does `c x ≠ c y` hold but also `c y ≠ c x`:

```lean
lemma ProperOn.symm {S : Finset V} {k : ℕ} {c : V → Fin k}
    (h : G.ProperOn S k c) {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (hadj : G.adj x y) : c y ≠ c x
```

**Hint:** Use `G.symm` to flip the adjacency, then apply `h` to the swapped arguments. `Ne.symm` may also be helpful.

### Exercise 2: Monotonicity of Proper Coloring

Prove that a proper coloring on a larger set is also proper on any subset:

```lean
lemma ProperOn.mono {S T : Finset V} {k : ℕ} {c : V → Fin k}
    (h : G.ProperOn T k c) (hST : S ⊆ T) : G.ProperOn S k c
```

**Hint:** Unfold `ProperOn` and use `hST` to lift membership from `S` to `T`, then apply `h`.

### Exercise 3: Pigeonhole Principle for Finite Types

Complete the proof of:
```lean
theorem nodup_length_le_card {l : List V} (hl : l.Nodup) :
    l.length ≤ Fintype.card V
```

**Hint:** Use `List.toFinset` and `Finset.card_le_univ`.

### Exercise 4: Properties of `dropTo`

Prove that dropping to a vertex produces a walk no longer than the original:
```lean
theorem length_dropTo_le {u v : V} (p : Walk (G := G) u v) (x : V)
    (hx : x ∈ p.toList) :
    (p.dropTo x hx).length ≤ p.length
```

**Hint:** Use induction on the walk `p` and case analysis on whether `x` equals the starting vertex.

## 6. Summary

In this lecture, we:
* Defined simple undirected graphs as structures with symmetric, loopless adjacency relations
* Proved a graph coloring theorem: any graph with maximum degree `D` is `(D+1)`-colorable
* Defined walks as inductive types and proved properties about walk composition
* Showed that any walk can be shortened to have length less than the number of vertices

These results demonstrate key proof techniques in Lean:
* Induction on finsets (`Finset.induction_on`)
* Strong induction on natural numbers (`Nat.strong_induction_on`)
* Case analysis with `by_cases`
* Working with decidable relations
* The pigeonhole principle for finite types

### New Techniques and Tactics Introduced in This Lecture

This lecture introduced several advanced techniques that weren't covered extensively in previous lectures:

**1. `classical`**
* Enables classical reasoning by making all propositions decidable
* Allows use of `by_cases` on arbitrary propositions
* Needed for computational operations on finite sets (like taking images of functions)

**2. `rcases ... with ⟨x, y, z⟩`**
* Powerful destructuring version of `cases`
* Simultaneously performs case analysis and extracts components
* Particularly useful for existential statements and conjunction

**3. `simpa`**
* Combines `simp` with `assumption` or `rfl`
* Simplifies the goal and tries to close it immediately
* Useful when simplification makes the goal trivial

**4. `cast`**
* Converts between definitionally equal types
* Essential when working with dependent types where types depend on values
* Often appears with `by rw [h]` to apply an equality proof

**5. `Function.update`**
* Creates a new function by updating one value
* Key lemmas: `Function.update_self` and `Function.update_of_ne`
* Useful for constructive proofs that build new objects from old ones

**6. Strong Induction Pattern**
* Define a predicate `P : ℕ → Prop`
* Prove `∀ n, P n` using `Nat.strong_induction_on`
* Induction hypothesis gives access to *all* smaller cases, not just `n-1`
* Essential when recursion doesn't decrease by exactly 1

**7. `Finset.induction_on`**
* Structural induction on finite sets
* Two cases: empty set and inserting an element
* Natural way to prove properties about all finite subsets

**8. Working with Dependent Types**
* `Walk : V → V → Type u` is indexed by two vertices
* Return types can depend on values (e.g., `Walk x v` depends on `x`)
* Requires careful use of `cast` and type equality proofs

**9. `rename_i`**
* Renames automatically-generated names in the context
* Useful when Lean's automatic naming isn't clear
* Example: `rename_i u v w` gives explicit names to constructor indices

**10. Proof by Contradiction with Case Analysis**
* Combine `by_cases` with proof by contradiction
* Show that all cases lead to contradictions except one
* Used in the pigeonhole argument for walk shortening

### Connections to Previous Lectures

* **Lecture 1-2:** Basic tactics (`intro`, `exact`, `apply`, `rw`, `simp`) remain fundamental
* **Lecture 2:** Induction on `Nat` and custom types extends to `Finset` induction
* **Lecture 3:** Logic tactics (`constructor`, `cases`, `left`, `right`) used throughout
* **Lecture 4:** Finite types and decidability extend to graph theory context

Graph theory in Lean is an active area of development, with applications to:
* Network algorithms and complexity
* Combinatorial optimization
* Formal verification of graph algorithms
* Structural graph theory (e.g., graph minors, planarity)

The techniques learned here form the foundation for formalizing more advanced results in graph theory and combinatorics.
