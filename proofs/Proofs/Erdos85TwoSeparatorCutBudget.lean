import Proofs.Erdos85DefectTwoVertexConnected
import Proofs.Erdos85TwoSeparatorMinimumCutResidue
import Proofs.Erdos85BranchDeficitSymmetry

/-!
# Cut budget across a two-vertex separator

If two shores have no edges between them and, together with a two-vertex
separator, cover a regular graph, then both shore boundaries are served by
the separator. Their total size is therefore at most twice the degree.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Generic two-separator cut budget in an `r`-regular graph. -/
theorem add_finsetGraphCutSize_le_two_mul_degree_of_twoSeparator
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (S T W : Finset V) {r : ℕ}
    (hcover : S ∪ T ∪ W = Finset.univ)
    (hST : Disjoint S T)
    (hno : ∀ s ∈ S, ∀ t ∈ T, ¬ D.Adj s t)
    (hWcard : W.card = 2) (hreg : ∀ x, D.degree x = r) :
    finsetGraphCutSize D S + finsetGraphCutSize D T ≤ 2 * r := by
  have hSsub : ∀ s ∈ S, D.neighborFinset s \ S ⊆ W := by
    intro s hs z hz
    have hzN := (Finset.mem_sdiff.mp hz).1
    have hznotS := (Finset.mem_sdiff.mp hz).2
    have hzcover : z ∈ S ∪ T ∪ W := by rw [hcover]; simp
    rcases Finset.mem_union.mp hzcover with hzST | hzW
    · rcases Finset.mem_union.mp hzST with hzS | hzT
      · exact (hznotS hzS).elim
      · exact (hno s hs z hzT
          ((SimpleGraph.mem_neighborFinset D s z).mp hzN)).elim
    · exact hzW
  have hTsub : ∀ t ∈ T, D.neighborFinset t \ T ⊆ W := by
    intro t ht z hz
    have hzN := (Finset.mem_sdiff.mp hz).1
    have hznotT := (Finset.mem_sdiff.mp hz).2
    have hzcover : z ∈ S ∪ T ∪ W := by rw [hcover]; simp
    rcases Finset.mem_union.mp hzcover with hzST | hzW
    · rcases Finset.mem_union.mp hzST with hzS | hzT
      · exact (hno z hzS t ht
          ((D.adj_comm t z).mp
            ((SimpleGraph.mem_neighborFinset D t z).mp hzN))).elim
      · exact (hznotT hzT).elim
    · exact hzW
  have hScut : finsetGraphCutSize D S ≤
      ∑ s ∈ S, (D.neighborFinset s ∩ W).card := by
    unfold finsetGraphCutSize
    apply Finset.sum_le_sum
    intro s hs
    apply Finset.card_le_card
    intro z hz
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hz).1, hSsub s hs hz⟩
  have hTcut : finsetGraphCutSize D T ≤
      ∑ t ∈ T, (D.neighborFinset t ∩ W).card := by
    unfold finsetGraphCutSize
    apply Finset.sum_le_sum
    intro t ht
    apply Finset.card_le_card
    intro z hz
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hz).1, hTsub t ht hz⟩
  have hswapS := sum_card_neighbor_inter_comm D S W
  have hswapT := sum_card_neighbor_inter_comm D T W
  have hpoint : ∀ w ∈ W,
      (D.neighborFinset w ∩ S).card + (D.neighborFinset w ∩ T).card ≤ r := by
    intro w _
    have hdisj : Disjoint (D.neighborFinset w ∩ S)
        (D.neighborFinset w ∩ T) :=
      hST.mono Finset.inter_subset_right Finset.inter_subset_right
    calc
      (D.neighborFinset w ∩ S).card + (D.neighborFinset w ∩ T).card =
          ((D.neighborFinset w ∩ S) ∪
            (D.neighborFinset w ∩ T)).card :=
        (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (D.neighborFinset w).card := Finset.card_le_card (by
        intro z hz
        rcases Finset.mem_union.mp hz with hz | hz <;>
          exact (Finset.mem_inter.mp hz).1)
      _ = r := by rw [D.card_neighborFinset_eq_degree, hreg w]
  calc
    finsetGraphCutSize D S + finsetGraphCutSize D T ≤
        (∑ s ∈ S, (D.neighborFinset s ∩ W).card) +
          ∑ t ∈ T, (D.neighborFinset t ∩ W).card :=
      Nat.add_le_add hScut hTcut
    _ = (∑ w ∈ W, (D.neighborFinset w ∩ S).card) +
          ∑ w ∈ W, (D.neighborFinset w ∩ T).card := by
      rw [hswapS, hswapT]
    _ = ∑ w ∈ W,
          ((D.neighborFinset w ∩ S).card +
            (D.neighborFinset w ∩ T).card) := by
      rw [Finset.sum_add_distrib]
    _ ≤ ∑ _w ∈ W, r := Finset.sum_le_sum hpoint
    _ = 2 * r := by simp [hWcard]

#print axioms add_finsetGraphCutSize_le_two_mul_degree_of_twoSeparator

end

end Erdos85
