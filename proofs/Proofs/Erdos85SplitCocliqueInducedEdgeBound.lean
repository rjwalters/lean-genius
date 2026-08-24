import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Edge bound for a split into two cocliques

This is the generic graph-counting endpoint of the two-separator low-set
argument.  Once every nonisolated vertex lies in one of two disjoint
cocliques, every edge crosses the split and there are at most `|P||Q|`
edges.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A finite graph bipartite with displayed finset shores has at most the
product of their cardinalities many edges. -/
theorem card_edgeFinset_le_mul_of_isBipartiteWith
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (P Q : Finset V) (hbip : H.IsBipartiteWith P Q) :
    H.edgeFinset.card ≤ P.card * Q.card := by
  rw [← H.isBipartiteWith_sum_degrees_eq_card_edges hbip]
  calc
    (∑ v ∈ P, H.degree v) ≤ ∑ _v ∈ P, Q.card := by
      apply Finset.sum_le_sum
      intro v hv
      exact H.isBipartiteWith_degree_le hbip hv
    _ = P.card * Q.card := by simp

/-- If `P` and `Q` are disjoint cocliques and every other vertex is
isolated, then all graph edges cross from `P` to `Q`. -/
theorem isBipartiteWith_of_disjoint_cocliques_of_isolated_outside
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (P Q : Finset V) (hPQ : Disjoint P Q)
    (hP : ∀ ⦃u v⦄, u ∈ P → v ∈ P → ¬ H.Adj u v)
    (hQ : ∀ ⦃u v⦄, u ∈ Q → v ∈ Q → ¬ H.Adj u v)
    (hout : ∀ ⦃u⦄, u ∉ P → u ∉ Q → H.degree u = 0) :
    H.IsBipartiteWith P Q := by
  refine ⟨by simpa using hPQ, ?_⟩
  intro u v huv
  have hu : u ∈ P ∨ u ∈ Q := by
    by_contra hnot
    simp only [not_or] at hnot
    have hz := hout hnot.1 hnot.2
    have hpos : 0 < H.degree u :=
      (H.degree_pos_iff_exists_adj u).2 ⟨v, huv⟩
    omega
  have hv : v ∈ P ∨ v ∈ Q := by
    by_contra hnot
    simp only [not_or] at hnot
    have hz := hout hnot.1 hnot.2
    have hpos : 0 < H.degree v :=
      (H.degree_pos_iff_exists_adj v).2 ⟨u, huv.symm⟩
    omega
  rcases hu with huP | huQ <;> rcases hv with hvP | hvQ
  · exact False.elim (hP huP hvP huv)
  · exact Or.inl ⟨huP, hvQ⟩
  · exact Or.inr ⟨huQ, hvP⟩
  · exact False.elim (hQ huQ hvQ huv)

/-- Split-coclique edge upper bound.  The optional center in the intended
application is simply one of the vertices covered by `hout`. -/
theorem card_edgeFinset_le_splitCoclique_product
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (P Q : Finset V) (hPQ : Disjoint P Q)
    (hP : ∀ ⦃u v⦄, u ∈ P → v ∈ P → ¬ H.Adj u v)
    (hQ : ∀ ⦃u v⦄, u ∈ Q → v ∈ Q → ¬ H.Adj u v)
    (hout : ∀ ⦃u⦄, u ∉ P → u ∉ Q → H.degree u = 0) :
    H.edgeFinset.card ≤ P.card * Q.card := by
  exact card_edgeFinset_le_mul_of_isBipartiteWith H P Q
    (isBipartiteWith_of_disjoint_cocliques_of_isolated_outside
      H P Q hPQ hP hQ hout)

end

end Erdos85

#print axioms Erdos85.card_edgeFinset_le_mul_of_isBipartiteWith
#print axioms Erdos85.card_edgeFinset_le_splitCoclique_product
