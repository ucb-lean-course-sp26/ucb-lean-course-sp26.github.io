/-
  CS 294-268 (Spring 2026)
  Homework 3 Solutions: Graph Theory in Lean

  Topics practiced:
  - Graph coloring and the ProperOn predicate
  - Symmetry and monotonicity of proper colorings
  - The pigeonhole principle for finite types
  - Dependent inductive types (Walk)
  - Induction on walks and case analysis
  - Reachability as an equivalence relation (Setoid / Quotient)
-/

import Mathlib
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Function.Basic

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

-- =================================================================
-- GRAPH AND COLORING DEFINITIONS (from lecture)
-- =================================================================

structure MyGraph (V : Type u) where
  adj : V → V → Prop
  symm : Symmetric adj
  loopless : Irreflexive adj

namespace MyGraph

variable {G : MyGraph V} [DecidableRel G.adj]

def neighbors (v : V) : Finset V := Finset.univ.filter (G.adj v)

def degree (v : V) : ℕ := (G.neighbors v).card

/-
  A coloring `c : V → Fin k` is **proper on S** if no two adjacent
  vertices in S share the same color.
-/
def ProperOn (S : Finset V) (k : ℕ) (c : V → Fin k) : Prop :=
  ∀ {x y}, x ∈ S → y ∈ S → G.adj x y → c x ≠ c y

-- =================================================================
-- PART 1: PROPERTIES OF PROPER COLORINGS
-- =================================================================

/-
  Task 1: Symmetry of proper coloring.

  A proper coloring gives `c x ≠ c y`; show it also gives `c y ≠ c x`.

  Tactics: `intro`, `apply`, `exact`.
  Hint: Use `G.symm` to flip the adjacency relation (turning `adj x y`
  into `adj y x`), then apply `h`. Finally, use `Ne.symm` to flip the
  resulting inequality.
-/
lemma ProperOn.symm {S : Finset V} {k : ℕ} {c : V → Fin k}
    (h : G.ProperOn S k c) {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (hadj : G.adj x y) : c y ≠ c x := by
  exact Ne.symm (h hx hy hadj)

/-
  Task 2: Monotonicity of proper coloring.

  If a coloring is proper on a larger set T, it is proper on any subset S ⊆ T.

  Tactics: `intro`, `apply`, `exact`.
  Hint: Unfold `ProperOn`. Given membership in S, use `hST` to lift it
  to membership in T, then apply `h`.
-/
lemma ProperOn.mono {S T : Finset V} {k : ℕ} {c : V → Fin k}
    (h : G.ProperOn T k c) (hST : S ⊆ T) : G.ProperOn S k c := by
  intro x y hxS hyS hxy
  exact h (hST hxS) (hST hyS) hxy

-- =================================================================
-- WALK DEFINITIONS (from lecture)
-- =================================================================

inductive Walk : V → V → Type u
  | nil  {u : V} : Walk u u
  | cons {u v w : V} (h : G.adj u v) (p : Walk v w) : Walk u w

namespace Walk

def length : {u v : V} → Walk (G := G) u v → Nat
  | _, _, nil       => 0
  | _, _, cons _ p  => Nat.succ p.length

def append {u v w : V} :
    Walk (G := G) u v → Walk (G := G) v w → Walk (G := G) u w
  | .nil,      q => q
  | .cons h p, q => cons h (append p q)

def toList : {u v : V} → Walk (G := G) u v → List V
  | u, _, nil       => [u]
  | u, _, cons _ p  => u :: p.toList

@[simp] theorem length_toList {u v : V} (p : Walk (G := G) u v) :
    p.toList.length = p.length + 1 := by
  induction p with
  | nil => simp [toList, length]
  | cons h p ih => simp [toList, length, ih, Nat.add_assoc]

def dropTo {u v : V} (p : Walk (G := G) u v) (x : V)
    (hx : x ∈ p.toList) : Walk (G := G) x v :=
  match p with
  | nil =>
    have h : x = u := by simpa [toList] using hx
    cast (by rw [h]) nil
  | cons h_adj p_rest =>
    if h_eq : u = x then
      cast (by rw [h_eq]) (cons h_adj p_rest)
    else
      dropTo p_rest x (by
        simp [toList] at hx
        cases hx with
        | inl h_is_u => subst h_is_u; contradiction
        | inr h_in_rest => exact h_in_rest)

-- =================================================================
-- PART 2: PIGEONHOLE PRINCIPLE FOR LISTS
-- =================================================================

/-
  Task 3: Pigeonhole principle for finite types.

  A duplicate-free list of elements from a finite type V has at most
  |V| elements.

  Tactics: `calc`, `simp`, `apply`, `exact`.
  Hint: Convert the list to a `Finset` using `List.toFinset`.
  The key lemmas are:
    - `List.toFinset_card_of_nodup : l.Nodup → l.toFinset.card = l.length`
    - `Finset.card_le_univ : s.card ≤ Fintype.card V`
-/
theorem nodup_length_le_card {l : List V} (hl : l.Nodup) :
    l.length ≤ Fintype.card V := by
  have hcard : l.toFinset.card ≤ Fintype.card V :=
    Finset.card_le_univ l.toFinset
  have hlen : l.length = l.toFinset.card :=
    (List.toFinset_card_of_nodup hl).symm
  simpa [hlen] using hcard

-- =================================================================
-- PART 3: PROPERTIES OF dropTo
-- =================================================================

/-
  Task 4: `dropTo` does not increase walk length.

  The suffix walk produced by `dropTo p x hx` is no longer than the
  original walk `p`.

  Tactics: `induction`, `simp`, `split`, `exact`, `apply`, `le_trans`.
  Hint: Use induction on `p`. In the `cons` case, split on whether
  `u = x` (the starting vertex):
    - If `u = x`, we return the whole walk (cast), so the length is equal.
    - If `u ≠ x`, we recurse into the tail. Use `le_trans` with
      `Nat.le_succ` to combine the inductive hypothesis with the fact
      that `cons` adds one step.

  You may find `simp [dropTo]` and `simp [length]` helpful for
  unfolding definitions.
-/
theorem length_dropTo_le {u v : V} (p : Walk (G := G) u v) (x : V)
    (hx : x ∈ p.toList) :
    (p.dropTo x hx).length ≤ p.length := by
  classical
  induction p with
  | nil =>
      -- hx : x ∈ [u], so x = u; after rewriting the cast is trivial
      rcases (by simpa [Walk.toList] using hx) with rfl
      simp [Walk.dropTo, Walk.length]
  | cons h_adj p_rest ih =>
      rename_i u v w
      have hx' : x = u ∨ x ∈ p_rest.toList := by
        simpa [Walk.toList] using hx

      by_cases h_eq : u = x
      · -- x is the starting vertex: dropTo returns the whole walk (cast)
        subst h_eq
        simp [Walk.dropTo, Walk.length]
      · -- x is deeper: dropTo recurses into p_rest
        have h_rest : x ∈ p_rest.toList := by
          cases hx' with
          | inl hx0 => exact (h_eq hx0.symm).elim
          | inr ht  => exact ht

        have ih' : (p_rest.dropTo x h_rest).length ≤ p_rest.length :=
          ih h_rest

        simpa [Walk.dropTo, h_eq, Walk.length] using
          le_trans ih' (Nat.le_succ _)

end Walk

-- =================================================================
-- PART 4: REACHABILITY AND CONNECTED COMPONENTS
-- =================================================================

/-- `u` and `v` are reachable from each other if there is some walk between them. -/
def Reachable (u v : V) : Prop :=
  Nonempty (Walk (G := G) u v)

/-
  Task 5: Reachability is reflexive.
-/
theorem reachable_refl (u : V) : G.Reachable u u :=
  ⟨Walk.nil⟩

/-
  Task 6: Reachability is transitive.
-/
theorem reachable_trans {a b c : V} :
    G.Reachable a b → G.Reachable b c → G.Reachable a c := by
  intro ⟨p⟩ ⟨q⟩
  exact ⟨p.append q⟩

/-
  Task 7: Reachability is symmetric.

  We induct on the walk p : Walk a b.
  - nil: a = b, so Walk.nil gives Walk b b = Walk b a.
  - cons h_adj p_rest: edge a~v and walk v→b.
    IH gives walk b→v. Flip the edge to get Walk.cons (G.symm h_adj) nil : Walk v a.
    Append the two pieces: b→v→a.
-/
theorem reachable_symm {a b : V} :
    G.Reachable a b → G.Reachable b a := by
  intro ⟨p⟩
  induction p with
  | nil => exact ⟨Walk.nil⟩
  | cons h_adj p_rest ih =>
      -- ih : G.Reachable _ a  (walk from the intermediate vertex back to a)
      obtain ⟨q⟩ := ih
      -- one-edge walk from the neighbour back to a using the flipped edge
      exact ⟨q.append (Walk.cons (G.symm h_adj) Walk.nil)⟩

/-
  Task 8: Package reachability as a Setoid.
-/
def connSetoid : Setoid V where
  r     := G.Reachable
  iseqv := ⟨reachable_refl (G := G),
            fun h => reachable_symm (G := G) h,
            fun h1 h2 => reachable_trans (G := G) h1 h2⟩

abbrev Component : Type u := Quotient (G.connSetoid)

def compOf (v : V) : G.Component := Quotient.mk G.connSetoid v

/-
  Task 9: Reachable vertices lie in the same component.
-/
theorem compOf_eq_of_reachable {a b : V} (h : G.Reachable a b) :
    G.compOf a = G.compOf b :=
  Quotient.sound h

end MyGraph
