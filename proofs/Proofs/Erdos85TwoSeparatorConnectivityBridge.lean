import Proofs.Erdos85TwoSeparatorShoreExtraction

/-!
# From a partition obstruction to two-vertex-deletion connectivity

Once explicit two-shore separator partitions are impossible, the canonical
shore extraction immediately shows that deleting any two vertices leaves a
connected graph.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A graph with at least three vertices whose explicit two-separator shore
partitions are all impossible remains connected after deleting any two-set. -/
theorem induce_sdiff_connected_of_no_twoSeparator_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hobstruct : ∀ (S T W : Finset V),
      S.Nonempty → T.Nonempty →
      S ∪ T ∪ W = Finset.univ → Disjoint S T →
      (∀ s ∈ S, ∀ t ∈ T, ¬ D.Adj s t) → W.card = 2 → False) :
    ∀ W : Finset V, W.card = 2 →
      (D.induce (↑(Finset.univ \ W) : Set V)).Connected := by
  intro W hWcard
  let U : Finset V := Finset.univ \ W
  let H := D.induce (↑U : Set V)
  have hUcard : U.card = Fintype.card V - 2 := by
    dsimp only [U]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ W),
      Finset.card_univ, hWcard]
  have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
  have hnonempty : Nonempty {z : V // z ∈ (↑U : Set V)} := by
    obtain ⟨z, hz⟩ := hUne
    exact ⟨⟨z, hz⟩⟩
  have hpre : H.Preconnected := by
    by_contra hnot
    obtain ⟨S, T, hSne, hTne, hcover, hST, hno, _hcards⟩ :=
      exists_ambient_shores_card_sum_of_two_vertex_deletion D W hWcard
        (by simpa [H, U] using hnot)
    exact hobstruct S T W hSne hTne hcover hST hno hWcard
  letI : Nonempty {z : V // z ∈ (↑U : Set V)} := hnonempty
  exact ⟨hpre⟩

end

end Erdos85

#print axioms Erdos85.induce_sdiff_connected_of_no_twoSeparator_partition
