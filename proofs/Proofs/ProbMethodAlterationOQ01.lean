/-
  Alteration / Deletion Bound: α(G) ≥ n − m   (verified, 0-axiom)

  Open Question OQ-01 from `prob-method-alteration`.

  The base entry `ProbMethodAlteration.lean` states its independent-set bound only in
  a vacuous "existence form",
        `independent_set_bound : ∃ k, k ≥ n / (2 * d) ∧ k > 0`,
  which never mentions a graph and is therefore trivially true.  This file replaces
  that placeholder with the genuine, purest instance of the deletion method, proved
  against the real independence number `α(G) = sSup {|S| : S independent}` (the same
  definition used in `ProbMethodAlterationOQ02` / `OQ03`):

        For every finite simple graph G on n vertices with m edges,
              α(G) ≥ n − m.

  Proof (deletion method, no probability needed).  Delete ONE endpoint from every
  edge.  Concretely, from each edge pick its lesser endpoint (a symmetric choice,
  hence well-defined on `Sym2 V` via `Sym2.lift ⟨min, min_comm⟩`).  The deleted set
  `D` satisfies `|D| ≤ m`, and its complement `univ \ D` is independent: any surviving
  edge would have kept both endpoints, contradicting that its lesser endpoint was
  deleted.  Thus `univ \ D` is an independent set of size `≥ n − m`.

  This is the WEAK end of the alteration spectrum (tight for a perfect matching,
  where `m = n/2` and `α = n/2`).  The classical STRONG bound `α(G) ≥ n²/(4m)` comes
  instead from random *sub-sampling* — keep each vertex with probability `p`, then
  delete a surviving endpoint per edge — leaving `n·p − m·p²` vertices in expectation.
  We record the arithmetic heart of that optimization (`sample_delete_le` /
  `sample_delete_attained`) as a companion; bridging it to the graph requires the
  probabilistic existence step, documented as the remaining gap.

  Status: verified, 0 axioms (only Lean/Mathlib foundations).
-/

import Mathlib

namespace ProbMethod.Deletion

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The independence number `α(G)`: the size of the largest independent set.
    (Same definition as in `ProbMethodAlterationOQ02` / `OQ03`.) -/
noncomputable def independenceNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ s : Finset V, s.card = k ∧
    ∀ v ∈ s, ∀ w ∈ s, v ≠ w → ¬G.Adj v w }

/-- The lesser endpoint of an edge: a symmetric choice function on `Sym2 V`. -/
noncomputable def pick : Sym2 V → V := Sym2.lift ⟨min, min_comm⟩

@[simp] theorem pick_mk (a b : V) : pick s(a, b) = min a b := rfl

/-- The chosen endpoint of an edge is one of its two endpoints. -/
theorem pick_mem_pair (a b : V) : pick s(a, b) = a ∨ pick s(a, b) = b := by
  rw [pick_mk]
  rcases le_total a b with h | h
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (min_eq_right h)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Vertices chosen for deletion: the lesser endpoint of each edge. -/
noncomputable def deletionSet : Finset V := G.edgeFinset.image pick

/-- At most one vertex is deleted per edge, so `|D| ≤ m`. -/
theorem deletionSet_card_le : (deletionSet G).card ≤ G.edgeFinset.card :=
  Finset.card_image_le

/-- **Independence of the complement.**  The complement of the deletion set contains
    no edge: if it did, that edge's chosen endpoint would have been deleted. -/
theorem indep_compl_deletionSet :
    ∀ a ∈ (univ \ deletionSet G), ∀ b ∈ (univ \ deletionSet G), a ≠ b →
      ¬ G.Adj a b := by
  intro a ha b hb _ hadj
  rw [Finset.mem_sdiff] at ha hb
  have hedge : s(a, b) ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]; exact (G.mem_edgeSet).mpr hadj
  have hpick : pick s(a, b) ∈ deletionSet G := Finset.mem_image_of_mem pick hedge
  -- The chosen endpoint is `a` or `b`; both are supposed to be undeleted.
  rcases pick_mem_pair a b with h | h
  · rw [h] at hpick; exact ha.2 hpick
  · rw [h] at hpick; exact hb.2 hpick

/-- **Alteration / deletion bound.**  For every finite simple graph,
    `α(G) ≥ (number of vertices) − (number of edges)`. -/
theorem independenceNumber_ge_card_sub_edges :
    Fintype.card V - G.edgeFinset.card ≤ independenceNumber G := by
  set P : Set ℕ := { k : ℕ | ∃ s : Finset V, s.card = k ∧
    ∀ v ∈ s, ∀ w ∈ s, v ≠ w → ¬G.Adj v w } with hP
  set S : Finset V := univ \ deletionSet G with hS
  -- `S` is an independent set, so `|S| ∈ P`.
  have hSmem : S.card ∈ P := ⟨S, rfl, indep_compl_deletionSet G⟩
  -- `P` is bounded above by `|V|`.
  have hbdd : BddAbove P := by
    refine ⟨Fintype.card V, ?_⟩
    intro k hk
    obtain ⟨s, rfl, -⟩ := hk
    exact Finset.card_le_univ s
  have hle : S.card ≤ independenceNumber G := le_csSup hbdd hSmem
  -- Lower bound on `|S| = n − |D| ≥ n − m`.
  have hScard : Fintype.card V - G.edgeFinset.card ≤ S.card := by
    have hcard : S.card = Fintype.card V - (deletionSet G).card := by
      rw [hS, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    rw [hcard]
    exact Nat.sub_le_sub_left (deletionSet_card_le G) _
  exact hScard.trans hle

-- ═══════════════════════════════════════════════════
--  Companion: the sub-sampling optimization behind α(G) ≥ n²/(4m)
-- ═══════════════════════════════════════════════════

/-- **Alteration optimization identity.**  Keeping each vertex with probability `p`
    and deleting one endpoint of every surviving edge leaves `n·p − m·p²` vertices in
    expectation.  Completing the square exhibits the maximum. -/
theorem sample_delete_optimum (n m p : ℝ) (hm : 0 < m) :
    n * p - m * p ^ 2 = n ^ 2 / (4 * m) - m * (p - n / (2 * m)) ^ 2 := by
  have hm' : m ≠ 0 := ne_of_gt hm
  field_simp
  ring

/-- The expected surplus `n·p − m·p²` never exceeds `n²/(4m)`. -/
theorem sample_delete_le (n m p : ℝ) (hm : 0 < m) :
    n * p - m * p ^ 2 ≤ n ^ 2 / (4 * m) := by
  rw [sample_delete_optimum n m p hm]
  have : 0 ≤ m * (p - n / (2 * m)) ^ 2 := mul_nonneg hm.le (sq_nonneg _)
  linarith

/-- The maximum `n²/(4m)` is attained at `p = n/(2m)`. -/
theorem sample_delete_attained (n m : ℝ) (hm : 0 < m) :
    n * (n / (2 * m)) - m * (n / (2 * m)) ^ 2 = n ^ 2 / (4 * m) := by
  rw [sample_delete_optimum n m (n / (2 * m)) hm]; ring

end ProbMethod.Deletion

-- Axiom audit: expect only propext / Classical.choice / Quot.sound.
#print axioms ProbMethod.Deletion.independenceNumber_ge_card_sub_edges
#print axioms ProbMethod.Deletion.sample_delete_optimum
#print axioms ProbMethod.Deletion.sample_delete_attained
