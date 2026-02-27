
import Mathlib
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Function.Basic

/-!
# Lecture 5: Introduction to Graphs in Lean

In this file we formalize two results in graph theory:

1. **Graph Coloring Theorem** – every graph with maximum degree D is (D+1)-colorable.
2. **Short Walk Theorem** – any walk between two vertices can be shortened to
   have length strictly less than the number of vertices in the graph.

These results demonstrate several important Lean proof techniques:
  * Induction on finite sets (`Finset.induction_on`)
  * Strong induction on natural numbers (`Nat.strong_induction_on`)
  * Case analysis (`by_cases`)
  * The pigeonhole principle for finite types
  * Dependent types and `cast`
-/

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-!
## Part 1: Graph Definition

We represent a **simple undirected loopless graph** as a structure containing:
* an adjacency relation `adj : V → V → Prop`
* a proof that the relation is **symmetric** (undirected edges)
* a proof that the relation is **irreflexive** (no self-loops)

This relational representation is natural for theorem proving – the structural
properties are baked in by construction, so we never need to re-establish them.
-/



structure MyGraph (V : Type u) where
  adj : V → V → Prop
  symm : Symmetric adj       -- adj x y → adj y x
  loopless : Irreflexive adj  -- ¬ adj x x



--- MORE DETAILS ON THE DEFINITION ---


/-
def Symmetric {V : Type*} (R : V → V → Prop) : Prop :=
  ∀ ⦃x y : V⦄, R x y → R y x

def Irreflexive {V : Type*} (R : V → V → Prop) : Prop :=
  ∀ (x : V), ¬ R x x

When you define the structure SimpleGraph, symm is a field that stores
a proof of the property Symmetric Adj.
Because proofs are first-class objects in Lean, G.symm is an object
whose type is the theorem (proposition) Symmetric Adj.

So, when you have a graph G, G.symm is a function/object that takes
three arguments:
    Two vertices: x and y.
    A proof/evidence: h (that G.Adj x y is true).
And it returns:
     A proof/evidence: (that G.Adj y x is true).

Because G.symm is an object of that function type,
you use it just like a function in your tactics or terms:

-- Suppose we have:
-- x y : V
-- h : G.Adj x y

-- have h_rev : G.Adj y x := G.symm h

  -/

--- Here is a definition of the complete graph

def completeGraph (V : Type u) : SimpleGraph V := {
  Adj := λ x y => x ≠ y,
  symm := λ x y h => h.symm,
  loopless := λ x h => h rfl  -- Constructing the loopless object here
}

/-Breaking down h rfl:

    rfl is the proof that x = x.
    h is the assumption that x ≠ x (which is the same as x = x → False).
    By passing rfl into h, you get a proof of False.
    Since the goal of loopless is to show Adj x x → False,
    this function fits the type perfectly.
    -/


namespace MyGraph

-- We work with a fixed graph G whose adjacency is decidable.
-- `DecidableRel G.adj` is needed so Lean can evaluate `Finset.filter (G.adj v)`.

variable {G : MyGraph V} [DecidableRel G.adj]

/-!
## Part 2: Graph Coloring
-/

-- The **neighbors** of a vertex v are all vertices adjacent to v.
-- We compute this as a `Finset` by filtering over all vertices.
def neighbors (v : V) : Finset V := Finset.univ.filter (G.adj v)

--#check neighbors

-- The **degree** of v is the number of its neighbors.
def degree (v : V) : ℕ := (G.neighbors v).card

#check degree

/-!
### Proper Coloring

A coloring `c : V → Fin k` assigns one of k colors to each vertex.
It is **proper on S** if no two adjacent vertices in S share a color.
-/


-- def ProperOn (S : Finset V) (k : ℕ) (c : V → Fin k) : Prop :=
def ProperOn (S : Finset V) (k : ℕ) (c : V → Fin k) : Prop :=
  ∀ {x y}, x ∈ S → y ∈ S → G.adj x y → c x ≠ c y

/-!
### Exercise 1 (Homework): Symmetry of ProperOn

A proper coloring gives `c x ≠ c y`; show it also gives `c y ≠ c x`.

Hint: use `G.symm` to flip the adjacency and `Ne.symm` to flip the inequality.
-/
lemma ProperOn.symm {S : Finset V} {k : ℕ} {c : V → Fin k}
    (h : G.ProperOn S k c) {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (hadj : G.adj x y) : c y ≠ c x := by
  sorry

/-!
### Exercise 2 (Homework): Monotonicity of ProperOn

If a coloring is proper on a larger set T, it is proper on any subset S ⊆ T.

Hint: unfold ProperOn; use `hST` to lift membership, then apply `h`.
-/
lemma ProperOn.mono {S T : Finset V} {k : ℕ} {c : V → Fin k}
    (h : G.ProperOn T k c) (hST : S ⊆ T) : G.ProperOn S k c := by
  sorry

/-!
### Key Lemma: Finding an Available Color

If vertex v has degree ≤ D and we have D+1 colors available, then
at least one color is not used by any neighbor of v.

**Proof idea (pigeonhole):**
* Let `forbidden` = {colors used by neighbors of v}
* |forbidden| ≤ degree(v) ≤ D  (image of a set has at most as many elements)
* Total colors = D+1 > D ≥ |forbidden|
* So some color is not forbidden.
-/
lemma exists_color_not_in_neighbors (D : ℕ) (v : V) (c : V → Fin (D + 1))
    (hdeg : G.degree v ≤ D) :
    ∃ col : Fin (D + 1), ∀ w ∈ G.neighbors v, col ≠ c w := by
  -- `classical` enables classical reasoning, needed for Finset.image over
  -- a function whose equality may not be decidable constructively.
  classical

  -- Step 1: Collect the colors forbidden for v (those used by neighbors).
  let forbidden : Finset (Fin (D + 1)) := (G.neighbors v).image c

  -- Step 2: Bound the number of forbidden colors.
  -- card(image c neighbors) ≤ card(neighbors) = degree v ≤ D
  have hforb : forbidden.card ≤ D :=
    (Finset.card_image_le).trans hdeg

  -- Step 3: Since D+1 > D ≥ |forbidden|, the full color palette is strictly bigger.
  -- `Fintype.card (Fin (D+1)) = D+1`, which simp knows.
  have hlt : forbidden.card < (Finset.univ : Finset (Fin (D + 1))).card := by
    simpa using (Nat.lt_succ_of_le hforb)

  -- Step 4: By pigeonhole, pick a color in univ but not in forbidden.
  -- `Finset.exists_mem_notMem_of_card_lt_card` says:
  --   if |A| < |B| then ∃ x ∈ B, x ∉ A
  rcases Finset.exists_mem_notMem_of_card_lt_card hlt with ⟨col, _hcolU, hcolNot⟩

  -- Step 5: Show this color is safe for all neighbors.
  refine ⟨col, ?_⟩
  -- We know col ∉ forbidden
  -- Now must prove for all nbrs w of v, col ≠ c w
  intro w hwN
  -- prove c w belongs to forbidden
  have : c w ∈ forbidden :=  by
    exact Finset.mem_image.2 ⟨w, hwN, rfl⟩
  -- if col = c w then col ∈ forbidden, contradiction
  intro hEq
  apply hcolNot
  simpa [hEq] using this


-- simpa use example

example {α : Type} [DecidableEq α] (s : Finset α) (a x : α)
    (hx : x ≠ a ∧ x ∈ s) : x ∈ s.erase a := by
  -- mem_erase: x ∈ s.erase a ↔ x ≠ a ∧ x ∈ s
  simpa [Finset.mem_erase] using hx
  --simp [Finset.mem_erase,hx] or
  -- simp [Finset.mem_erase]
  -- exact hx
/-!
### Extending a Partial Coloring

Given a proper coloring of `S \ {v}`, we can always extend it to include v.

**Proof outline:**
1. Find a safe color `new_col` for v using the previous lemma.
2. Update the coloring: `c' = Function.update c v new_col`
   (same as c everywhere except at v, where it returns new_col).
3. Verify c' is proper on all of S by double case analysis on whether
   the endpoints of each edge equal v.
-/
lemma extend_proper (D : ℕ) (S : Finset V) (v : V) (hv : v ∈ S)
    (hdeg : ∀ w, G.degree w ≤ D)
    (c : V → Fin (D + 1)) (hc : G.ProperOn (S.erase v) (D + 1) c) :
    ∃ c' : V → Fin (D + 1), G.ProperOn S (D + 1) c' := by
  -- 1. Get a safe color for v.
  obtain ⟨new_col, h_safe⟩ := exists_color_not_in_neighbors D v c (hdeg v)

  -- 2. Build the updated coloring c'.
  --    `Function.update c v new_col` returns new_col at v, and c x elsewhere.
  let c' := Function.update c v new_col

  -- use refine to prove existentially qualified statement
  refine ⟨c', ?_⟩

  -- 3. Check properness for every edge x~y with x,y ∈ S.
  intro x y hxS hyS hxy
  -- expand out how c' is defined
  dsimp [c']

  -- Case A: x = v
  by_cases hx : x = v
  · subst hx
    rw [Function.update_self]  -- c' v = new_col
    by_cases hy : y = x
    · subst hy
      -- Edge x~x is a self-loop — impossible by looplessness.
      exact (G.loopless y hxy).elim
    · -- Edge v~y with y ≠ v.
      rw [Function.update_of_ne hy]  -- c' y = c y
      -- h_safe says new_col ≠ c w for all neighbors w of v.
      apply h_safe
      simp [neighbors, hxy]

  · -- Case B: x ≠ v
    rw [Function.update_of_ne hx]  -- c' x = c x
    by_cases hy : y = v
    · subst hy
      rw [Function.update_self]
      apply Ne.symm
      apply h_safe
      -- Show x is a neighbor of v (using symmetry)
      simp [neighbors, G.symm hxy]
    · -- Case: x ≠ v, y ≠ v
      rw [Function.update_of_ne hy]
      apply hc
      · simp [Finset.mem_erase, hx, hxS]
      · simp [Finset.mem_erase, hy, hyS]
      · exact hxy




/-!
### Main Coloring Theorem


**Theorem:** Any finite graph with maximum degree D is (D+1)-colorable.

**Proof by induction on the vertex set S** using `Finset.induction_on`:
* **Base case (S = ∅):** The constant function works vacuously.
* **Inductive step (S = insert a s):**
  - By the IH, s has a proper coloring c.
  - Note (insert a s).erase a = s (since a ∉ s).
  - Apply `extend_proper` to extend c from s to insert a s.
-/
theorem colorable_of_degree_le (D : ℕ) (hdeg : ∀ v, G.degree v ≤ D) (S : Finset V) :
    ∃ c : V → Fin (D + 1), G.ProperOn S (D + 1) c := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      -- Base case: empty set. Any coloring works; ProperOn is vacuously true.
      exact ⟨fun _ => 0, by simp [ProperOn]⟩
  | @insert a s ha ih =>
      -- ih : ∃ c, ProperOn s (D+1) c
      rcases ih with ⟨c, hc⟩

      -- Record the fact: erasing a from (insert a s) recovers s (since a ∉ s).
      have hErase : (insert a s).erase a = s := by
        ext x
        by_cases hx : x = a
        · simp [hx, ha]
        · simp [Finset.mem_erase, hx]

      --- let us prepare the hypothesis needed to call extend_proper
      have ha_mem : a ∈ (insert a s) := Finset.mem_insert_self a s
      have hc' : G.ProperOn ((insert a s).erase a) (D + 1) c := by simpa [hErase]
      exact extend_proper (G := G) D (insert a s) a ha_mem hdeg c hc'


--- That concludes the proof! ---

/-!
## Part 3: Walks in Graphs

A **walk** from u to v is an alternating sequence of vertices and edges,
starting at u and ending at v.

We use an **inductive type** indexed by the two endpoints:
  `Walk u v` is the type of all walks from u to v.

This is a *dependent type* — the type itself encodes the endpoints,
so Lean statically guarantees correctness.
-/
inductive Walk : V → V → Type u
  | nil  {u : V} : Walk u u
    -- `nil` is the trivial walk from u to u (no edges, length 0)
  | cons {u v w : V} (h : G.adj u v) (p : Walk v w) : Walk u w
    -- `cons h p` prepends the edge u~v to a walk from v to w,
    -- giving a walk from u to w
deriving DecidableEq

#check Walk
#check Walk (G := G)

namespace Walk

/-!
### Walk Length

The length of a walk is its number of edges.
`Nat.succ` (rather than `+ 1`) is used so that pattern-matching
in later induction proofs stays clean.
-/
def length : {u v : V} → Walk (G := G) u v → Nat
  | _, _, nil       => 0
  | _, _, cons _ p  => Nat.succ p.length


/- Can also define Walk with G explicit:

inductive Walk (G : MyGraph V) : V → V → Type u
| nil  {u : V} : Walk G u u
| cons {u v w : V} (h : G.adj u v) (p : Walk G v w) : Walk G u w

Length then becomes
def length : {u v : V} → Walk G u v → Nat := ...

-/
/-!
### Appending Walks

Two walks can be composed end-to-end: if p : Walk u v and q : Walk v w
then `append p q : Walk u w`.

Defined by induction on the left walk p.

Below we are pulling out the implicit indices {u,v,w} on he left,
and then match only on the walk arguments
-/

def append {u v w : V} :
    Walk (G := G) u v → Walk (G := G) v w → Walk (G := G) u w
  |  .nil,       q => q
  |  .cons h p,  q => cons h (append p q)

/-!
**Length of appended walks** is the sum of individual lengths.
Proof by induction on the left walk.
-/
@[simp] theorem length_append {u v w : V}
    (p : Walk (G := G) u v) (q : Walk (G := G) v w) :
    (append p q).length = p.length + q.length := by
  induction p with
  | nil =>
      simp [append, length]
  | cons h p ih =>
      simp [append, length, ih, Nat.succ_add]

/-!
### Vertex List of a Walk

`toList p` lists all vertices visited by p (including both endpoints).
A walk of length L visits L+1 vertices.
-/
def toList : {u v : V} → Walk (G := G) u v → List V
  | u, _, nil       => [u]
  | u, _, cons _ p  => u :: p.toList

/-!
**Length of the vertex list** is always walk length + 1.
-/
@[simp] theorem length_toList {u v : V} (p : Walk (G := G) u v) :
    p.toList.length = p.length + 1 := by
  induction p with
  | nil =>
      simp [toList, length]
  | cons h p ih =>
      simp [toList, length, ih, Nat.add_assoc]


/-!
### Exercise 3 (Homework): Pigeonhole Principle for Lists

A duplicate-free list of vertices from a finite type V has at most |V| elements.

Hint: convert the list to a `Finset` using `List.toFinset`, then use
`List.toFinset_card_of_nodup` and `Finset.card_le_univ`.
-/
theorem nodup_length_le_card {l : List V} (hl : l.Nodup) :
    l.length ≤ Fintype.card V := by
  sorry


/-!
### `dropTo`: Suffix Walk Starting at a Given Vertex

`dropTo p x hx` takes a walk `p : Walk u v` and a vertex `x` that appears
in `p.toList`, and returns the suffix `Walk x v` starting from x.

This requires `cast` because the return type `Walk x v` depends on the
*value* `x` — even after we prove `x = u` in a branch, Lean's type checker
treats `Walk x v` and `Walk u v` as syntactically different types and needs
an explicit coercion.
-/
def dropTo {u v : V} (p : Walk (G := G) u v) (x : V)
    (hx : x ∈ p.toList) : Walk (G := G) x v :=
  match p with
  | nil =>
    -- The only vertex in `nil`'s list is u, so x = u.
    have h : x = u := by simpa [toList] using hx
    -- `cast (by rw [h]) nil` converts `Walk u u` to `Walk x u = Walk x v`
    cast (by rw [h]) nil
  | cons h_adj p_rest =>
    if h_eq : u = x then
      -- x is exactly the starting vertex — return the whole walk.
      cast (by rw [h_eq]) (cons h_adj p_rest)
    else
      -- x is somewhere deeper; recurse into the rest of the walk.
      dropTo p_rest x (by
        simp [toList] at hx
        cases hx with
        | inl h_is_u => subst h_is_u; contradiction
        | inr h_in_rest => exact h_in_rest)


/-!
### Exercise 4 (Homework): `dropTo` Does Not Increase Length

The suffix walk produced by `dropTo` is no longer than the original walk.

Hint: induction on `p`; split on `u = x` (the starting vertex of the walk).
If `u = x` we drop nothing, so length is equal. Otherwise we recurse and
apply `le_trans` with `Nat.le_succ`.
-/
theorem length_dropTo_le {u v : V} (p : Walk (G := G) u v) (x : V)
    (hx : x ∈ p.toList) :
    (p.dropTo x hx).length ≤ p.length := by
  sorry


/-!
### Splicing Lemma

If a walk visits some vertex twice, we can remove the "loop" between
the two visits to get a strictly shorter walk with the same endpoints.

**Proof by induction on the walk:**
* `nil`: the vertex list `[u]` has no duplicates — contradiction.
* `cons h_adj p_rest`: the list is `u :: p_rest.toList`. Either:
  - u appears again in `p_rest.toList` → use `dropTo` to skip to the
    second occurrence of u, giving a shorter walk.
  - `p_rest.toList` itself is not duplicate-free → apply the IH to
    shorten p_rest, then prepend the first edge.
-/
lemma exists_shorter_walk_of_not_nodup {u v : V} (p : Walk (G := G) u v) :
    ¬ p.toList.Nodup → ∃ (p' : Walk (G := G) u v), p'.length < p.length := by
  classical
  induction p with
  | nil =>
      -- [u] is always duplicate-free; the hypothesis is False.
      intro h; simpa [Walk.toList] using h
  | cons h_adj p_rest ih =>
      intro h_dup
      rename_i u v w
      -- Decompose: ¬ Nodup (u :: tail) means u ∈ tail ∨ ¬ Nodup tail.
      have hcases : u ∈ p_rest.toList ∨ ¬ p_rest.toList.Nodup := by
        have : ¬ (u ∉ p_rest.toList ∧ p_rest.toList.Nodup) := by
          simpa [Walk.toList, List.nodup_cons] using h_dup
        have : ¬ (u ∉ p_rest.toList) ∨ ¬ p_rest.toList.Nodup := not_and_or.mp this
        simpa using this

      cases hcases with
      | inl h_u_in_tail =>
          -- u appears again later — drop everything up to the second u.
          let p' : Walk (G := G) u w := p_rest.dropTo u h_u_in_tail
          refine ⟨p', ?_⟩
          have hle : p'.length ≤ p_rest.length :=
            by simpa [p'] using
              length_dropTo_le (G := G) (p := p_rest) (x := u) (hx := h_u_in_tail)
          simpa [p', Walk.length] using Nat.lt_succ_of_le hle
      | inr h_tail_dup =>
          -- The rest has a duplicate — shorten the rest by IH.
          obtain ⟨short_tail, h_len⟩ := ih h_tail_dup
          refine ⟨Walk.cons h_adj short_tail, ?_⟩
          simpa [Walk.length] using Nat.succ_lt_succ h_len


/-!
### Main Theorem: Short Walk Existence

For any walk from u to v, there exists a walk from u to v with length < |V|.

**Intuition:** A walk of length ≥ |V| visits ≥ |V|+1 vertices, but there are
only |V| vertices, so some vertex is visited twice. Remove the loop to shorten.
Repeat until the walk is short enough.

**Proof by strong induction on walk length:**

Strong induction is necessary because each shortening step may reduce the
length by more than 1 (we might remove a large loop), so we can't use the
simple `n → n+1` structure of regular induction.
-/
theorem exists_short_walk {u v : V} (p_orig : Walk (G := G) u v) :
    ∃ (p : Walk (G := G) u v), p.length < Fintype.card V := by
  classical

  -- Define the predicate we'll prove for all n by strong induction.
  -- P n = "every walk of length n has a short version"
  let P : ℕ → Prop :=
    fun n =>
      ∀ {u v : V} (p : Walk (G := G) u v), p.length = n →
        ∃ p' : Walk (G := G) u v, p'.length < Fintype.card V

  -- Prove P n for all n by strong induction.
  -- The strong IH gives us: ∀ m < n, P m.
  have hP : ∀ n, P n := by
    intro n0
    refine Nat.strong_induction_on n0 ?_
    intro n ih
    intro p hp_len

    -- Case 1: the walk is already short enough.
    by_cases h_small : p.length < Fintype.card V
    · exact ⟨p, h_small⟩

    -- Case 2: p.length ≥ |V|.
    -- Show p.toList must have a duplicate.
    · have h_not_nodup : ¬ p.toList.Nodup := by
        intro h_nodup
        have h1 : p.toList.length ≤ Fintype.card V :=
          nodup_length_le_card (V := V) h_nodup
        have h2 : p.length + 1 ≤ Fintype.card V := by
          simpa [Walk.length_toList] using h1
        have : p.length < Fintype.card V :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h2
        exact h_small this

      -- Get a strictly shorter walk with the same endpoints.
      obtain ⟨p_shorter, h_shorter_len⟩ :=
        exists_shorter_walk_of_not_nodup (G := G) p h_not_nodup

      -- p_shorter.length < p.length = n, so we can apply the IH.
      have hmn : p_shorter.length < n := by simpa [hp_len] using h_shorter_len
      exact ih p_shorter.length hmn p_shorter rfl

  -- Apply the proved predicate to the original walk.
  exact hP p_orig.length (u := u) (v := v) p_orig rfl


end Walk
end MyGraph
