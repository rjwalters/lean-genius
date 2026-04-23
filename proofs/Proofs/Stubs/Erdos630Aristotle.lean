/-
  Aristotle targets for Erdős Problem #630
  List Chromatic Number of Planar Bipartite Graphs
  Routine supporting lemmas for automated proof search.
  See Erdos630Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main results (Alon-Tarsi theorem — requires Combinatorial Nullstellensatz)
  - NOT theorems depending on def-sorries (listChromaticNumber, IsPlanar, graphPolynomial, IsOuterplanar)
  - Routine supporting facts: list coloring structure, 2^k arithmetic, basic graph properties
  - No definition sorries, no axioms, no open conjectures
  - All 13 lemmas proved
-/
import Mathlib

namespace Erdos630Aristotle

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A list assignment maps each vertex to a finite set of available colors. -/
def ListAssignment' (V C : Type*) := V → Finset C

/-- A list coloring respects the lists and is a proper graph coloring. -/
def IsListColoring' (G : SimpleGraph V) {C : Type*} [DecidableEq C]
    (L : ListAssignment' V C) (f : V → C) : Prop :=
  (∀ v : V, f v ∈ L v) ∧
  (∀ v w : V, G.Adj v w → f v ≠ f w)

/-- A graph is k-list-colorable if for any lists of size ≥ k a proper list coloring exists. -/
def IsKChoosable' (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (C : Type*) [DecidableEq C] (L : ListAssignment' V C),
    (∀ v : V, (L v).card ≥ k) →
    ∃ f : V → C, IsListColoring' G L f

-- Routine: A list coloring places each vertex's color in its assigned list.
-- Follows directly from the first component of the definition.
theorem list_coloring_mem (G : SimpleGraph V) {C : Type*} [DecidableEq C]
    (L : ListAssignment' V C) (f : V → C)
    (h : IsListColoring' G L f) (v : V) : f v ∈ L v :=
  h.1 v

-- Routine: A list coloring is a proper coloring (adjacent vertices get different colors).
-- Follows directly from the second component of the definition.
theorem list_coloring_proper (G : SimpleGraph V) {C : Type*} [DecidableEq C]
    (L : ListAssignment' V C) (f : V → C)
    (h : IsListColoring' G L f) (v w : V) (hadj : G.Adj v w) : f v ≠ f w :=
  h.2 v w hadj

-- Routine: A list coloring on the empty graph always exists.
-- No adjacency constraints, so any color selection from non-empty lists works.
theorem empty_graph_list_colorable (k : ℕ) (hk : 0 < k) :
    IsKChoosable' (⊥ : SimpleGraph V) k := by
  intro C _ L hsize
  have hne : ∀ v, (L v).Nonempty :=
    fun v => Finset.card_pos.mp (Nat.lt_of_lt_of_le hk (hsize v))
  exact ⟨fun v => (hne v).choose,
         ⟨fun v => (hne v).choose_spec, fun v w h => by simp at h⟩⟩

-- Routine: For any list assignment, if lists are non-empty then the union of all
-- lists is non-empty. (Needed for existence arguments.)
theorem list_assignment_union_nonempty {C : Type*} [DecidableEq C]
    (L : ListAssignment' V C) (v : V) (h : (L v).Nonempty) :
    (Finset.univ.biUnion L).Nonempty := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, hc⟩⟩

-- Routine: In the empty graph ⊥, any function is a proper coloring.
-- There are no edges, so the adjacency condition is vacuously satisfied.
theorem bot_proper_coloring {C : Type*} (f : V → C) :
    ∀ v w : V, (⊥ : SimpleGraph V).Adj v w → f v ≠ f w := by
  intro v w h; simp at h

-- Routine: No vertex is adjacent to itself (SimpleGraph is loopless).
-- This is part of the SimpleGraph definition.
theorem no_self_loop (G : SimpleGraph V) (v : V) : ¬G.Adj v v :=
  G.loopless v

-- Routine: Adjacency is symmetric.
-- This is part of the SimpleGraph definition.
theorem adj_symm (G : SimpleGraph V) (v w : V) (h : G.Adj v w) : G.Adj w v :=
  G.symm h

-- Routine: 0 < 2^k for all natural k.
-- A positive base raised to any power is positive.
theorem two_pow_pos (k : ℕ) : 0 < 2 ^ k :=
  Nat.pos_pow_of_pos k (by norm_num)

-- Routine: 1 ≤ 2^k for all natural k.
-- Follows from two_pow_pos.
theorem two_pow_ge_one (k : ℕ) : 1 ≤ 2 ^ k :=
  Nat.one_le_pow k 2 (by norm_num)

-- Routine: 2^(k-1) ≤ 2^k for all natural k.
-- Subtracting 1 from the exponent yields a smaller or equal power.
theorem two_pow_pred_le (k : ℕ) : 2 ^ (k - 1) ≤ 2 ^ k :=
  Nat.pow_le_pow_right (by norm_num) (Nat.sub_le k 1)

-- Routine: Nat.clog 2 n + 1 > 0 for all n.
-- Adding 1 to any natural number gives a positive result.
theorem clog_add_one_pos (n : ℕ) : 0 < Nat.clog 2 n + 1 := by
  omega

-- Routine: For n ≥ 2, Nat.clog 2 n ≥ 1.
-- The ceiling log base 2 of any number ≥ 2 is at least 1.
theorem clog_ge_one (n : ℕ) (hn : 2 ≤ n) : 1 ≤ Nat.clog 2 n := by
  have h0 : Nat.clog 2 n ≠ 0 := by
    rw [Nat.clog_eq_zero_iff]; omega
  omega

-- Routine: Fintype.card V ≥ 0.
-- Cardinality of a finite type is a natural number, hence ≥ 0.
theorem card_nonneg : 0 ≤ Fintype.card V := Nat.zero_le _

-- Routine: If a Finset has card ≥ k, it has card ≥ k - 1.
-- Subtracting 1 from a lower bound gives a weaker lower bound.
theorem card_ge_pred {α : Type*} (k : ℕ) (s : Finset α) (h : k ≤ s.card) :
    k - 1 ≤ s.card := by
  omega

end Erdos630Aristotle
