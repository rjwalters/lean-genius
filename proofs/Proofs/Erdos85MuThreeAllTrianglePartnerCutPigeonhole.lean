import Proofs.Erdos85MuThreeAllTriangleHCut

/-! # A row-partner pair receives two H-cut incidences -/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem graphCutIncidenceCount_compl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V)
    [DecidablePred (· ∈ S)] :
    graphCutIncidenceCount G S = graphCutIncidenceCount G Sᶜ := by
  classical
  rw [graphCutIncidenceCount, graphCutIncidenceCount]
  rw [← Finset.sum_subtype S.toFinset (by simp)
      (fun v : V => (G.neighborFinset v \ S.toFinset).card),
    ← Finset.sum_subtype Sᶜ.toFinset (by simp)
      (fun v : V => (G.neighborFinset v \ Sᶜ.toFinset).card)]
  convert (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := G.Adj) (s := S.toFinset) (t := Sᶜ.toFinset)) using 1
  · apply Finset.sum_congr rfl
    intro x hx
    congr 1
    ext y
    simp [SimpleGraph.neighborFinset_eq_filter, Finset.bipartiteAbove, and_comm]
  · apply Finset.sum_congr rfl
    intro x hx
    congr 1
    ext y
    simp [SimpleGraph.neighborFinset_eq_filter, Finset.bipartiteBelow,
      and_comm, G.adj_comm]

/-- If 32 objects are paired by a permutation and carry total weight at least
26, then some paired pair carries weight at least two.  This is the arithmetic
pigeonhole step used for row mates in the all-triangle sector. -/
theorem exists_two_le_pairWeight_of_card_thirtyTwo_sum_twentySix
    {A : Type*} [Fintype A] [DecidableEq A]
    (e : A ≃ A) (weight : A → ℕ)
    (hcard : Fintype.card A = 32)
    (hsum : 26 ≤ ∑ x : A, weight x) :
    ∃ x : A, 2 ≤ weight x + weight (e x) := by
  by_contra hnone
  push Not at hnone
  have hpairs : ∀ x : A, weight x + weight (e x) ≤ 1 := by
    intro x
    have hx := hnone x
    omega
  have htotal :
      (∑ x : A, (weight x + weight (e x))) ≤ ∑ _x : A, 1 := by
    apply Finset.sum_le_sum
    intro x _hx
    exact hpairs x
  have hreindex : (∑ x : A, weight (e x)) = ∑ x : A, weight x := by
    exact e.sum_comp weight
  have hones : (∑ _x : A, 1) = 32 := by
    simp [hcard]
  rw [Finset.sum_add_distrib, hreindex, hones] at htotal
  omega

end

end Erdos85

#print axioms Erdos85.graphCutIncidenceCount_compl
#print axioms Erdos85.exists_two_le_pairWeight_of_card_thirtyTwo_sum_twentySix
