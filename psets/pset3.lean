/-
  CS 294-268 (Spring 2026)
  Homework 3: Graph Theory in Lean

  Instructions:
  1. Replace every `sorry` with a valid proof.
  2. Prefer the tactics listed in each task.
  3. Submit your completed .lean file.

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
  sorry

/-
  Task 2: Monotonicity of proper coloring.

  If a coloring is proper on a larger set T, it is proper on any subset S ⊆ T.

  Tactics: `intro`, `apply`, `exact`.
  Hint: Unfold `ProperOn`. Given membership in S, use `hST` to lift it
  to membership in T, then apply `h`.
-/
lemma ProperOn.mono {S T : Finset V} {k : ℕ} {c : V → Fin k}
    (h : G.ProperOn T k c) (hST : S ⊆ T) : G.ProperOn S k c := by
  sorry

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
  sorry

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
  sorry

end Walk

-- =================================================================
-- PART 4: REACHABILITY AND CONNECTED COMPONENTS
-- =================================================================

/-
  Two vertices are **reachable** from one another if there exists a walk
  between them.  Because `Walk u v` is a type (not a proposition), we
  wrap it in `Nonempty` to get a proposition.

  This section shows that reachability is an *equivalence relation*,
  and uses Lean's `Setoid` / `Quotient` machinery to define connected
  components as a quotient type.
-/

/-- `u` and `v` are reachable from each other if there is some walk between them. -/
def Reachable (u v : V) : Prop :=
  Nonempty (Walk (G := G) u v)

/-
  Task 5: Reachability is reflexive.

  Every vertex can reach itself via the trivial (nil) walk.

  Tactics: `exact`, constructor notation.
  Hint: `Walk.nil` is the empty walk; wrap it with `⟨⟩`.
-/
theorem reachable_refl (u : V) : G.Reachable u u := by
  sorry

/-
  Task 6: Reachability is transitive.

  If there is a walk from `a` to `b` and a walk from `b` to `c`,
  then there is a walk from `a` to `c`.

  Tactics: `intro`, `obtain`, `exact`.
  Hint: Use `Walk.append` to concatenate the two walks.
  `Nonempty.elim` (or `obtain ⟨p, _⟩ := ...`) extracts a walk from
  a `Nonempty` proof.
-/
theorem reachable_trans {a b c : V} :
    G.Reachable a b → G.Reachable b c → G.Reachable a c := by
  sorry

/-
  Task 7: Reachability is symmetric.

  If there is a walk from `a` to `b`, then there is a walk from `b` to `a`.

  Tactics: `intro`, `obtain`, `induction`, `exact`.
  Hint: Proceed by induction on the walk `p : Walk a b`.
    - `nil` case: `a = b`, so `Walk.nil` works.
    - `cons` case: you have an edge `a ~ v` and a walk `v → b`.
      By the induction hypothesis you can get a walk `b → v`.
      Use `G.symm` to flip the edge `a ~ v` to `v ~ a`,
      then append the two pieces.
-/
theorem reachable_symm {a b : V} :
    G.Reachable a b → G.Reachable b a := by
  sorry

/-
  Task 8: Package reachability as a `Setoid`.

  A `Setoid V` is a structure that bundles an equivalence relation on `V`
  together with a proof that it is indeed an equivalence relation.

  Fill in the three fields using the lemmas above.
  The field `iseqv` expects a term of type `Equivalence G.Reachable`, which
  is a structure `⟨refl, symm, trans⟩`.

  Tactics: `exact`, `constructor`, or fill in the fields directly with
  term-mode proofs.
-/
def connSetoid : Setoid V where
  r     := G.Reachable
  iseqv := by
    constructor
    · -- reflexivity
      sorry
    · -- symmetry
      sorry
    · -- transitivity
      sorry

/-
  Connected components are the equivalence classes of `connSetoid`.
  `Quotient.mk` sends a vertex to its component.
-/
abbrev Component : Type u := Quotient (G.connSetoid)

def compOf (v : V) : G.Component := Quotient.mk G.connSetoid v

/-
  Task 9: Reachable vertices lie in the same component.

  `Quotient.sound` says: if `r a b` holds (for the `Setoid`'s relation),
  then `Quotient.mk _ a = Quotient.mk _ b`.

  Tactics: `exact`, `apply`.
  Hint: Apply `Quotient.sound` directly to `h`.
-/
theorem compOf_eq_of_reachable {a b : V} (h : G.Reachable a b) :
    G.compOf a = G.compOf b := by
  sorry

end MyGraph

