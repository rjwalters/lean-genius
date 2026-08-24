import Proofs.Erdos85OddSquareOrderNineArticulationGraphBridge

/-!
# Generic deleted-owner shore classification

This module extracts the graph-theoretic part of the order-nine articulation
argument with no order, degree, or profile specialization.  If `D[O]` is
connected but deleting an owner disconnects it, the two component shores are
nonempty, complementary and relatively closed.  When `E` is exactly the
owner neighborhood in `O`, both shores meet `E`, and their full ambient
boundaries are exactly their respective `E`-masses.

This is the reusable articulation interface for the general binary-square
`A-REG-NONBIP` program; later arithmetic may classify the two boundary
masses without rebuilding the component-selection layer.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A connected induced graph whose owner deletion disconnects admits two
nonempty complementary punctured shores.  Each shore is closed in the
deleted-owner graph, meets the owner neighborhood, and has ambient boundary
equal to the size of that intersection. -/
theorem exists_deletedOwner_complementary_shores_with_exact_boundaries
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (O E : Finset V) (owner : V)
    (hownerO : owner ∈ O)
    (hneighborsO : ∀ u ∈ O, D.neighborFinset u ⊆ O)
    (hownerAdj : ∀ u ∈ O, D.Adj u owner ↔ u ∈ E)
    (hconnected : (D.induce (↑O : Set V)).Connected)
    (hpuncturedNonempty : (O.erase owner).Nonempty)
    (hnot : ¬ (D.induce (↑(O.erase owner) : Set V)).Connected) :
    ∃ S T : Finset V,
      S.Nonempty ∧ T.Nonempty ∧
      S ∪ T = O.erase owner ∧ Disjoint S T ∧
      (∀ x ∈ S, D.neighborFinset x ∩ (O.erase owner) ⊆ S) ∧
      (∀ x ∈ T, D.neighborFinset x ∩ (O.erase owner) ⊆ T) ∧
      (E ∩ S).Nonempty ∧ (E ∩ T).Nonempty ∧
      (∑ x ∈ S,
        (D.neighborFinset x ∩ (Finset.univ \ S)).card) = (E ∩ S).card ∧
      (∑ x ∈ T,
        (D.neighborFinset x ∩ (Finset.univ \ T)).card) = (E ∩ T).card := by
  classical
  obtain ⟨S, T, hSnonempty, hTnonempty, hunion, hdisj, hSclosed, hTclosed⟩ :=
    exists_two_nonempty_complementary_relativeClosedShores_of_induce_not_connected
      D (O.erase owner) hpuncturedNonempty hnot
  have hSsubErase : S ⊆ O.erase owner := by
    intro x hx
    rw [← hunion]
    exact Finset.mem_union_left T hx
  have hTsubErase : T ⊆ O.erase owner := by
    intro x hx
    rw [← hunion]
    exact Finset.mem_union_right S hx
  have hSsub : S ⊆ O := fun _ hx => (Finset.mem_erase.mp (hSsubErase hx)).2
  have hTsub : T ⊆ O := fun _ hx => (Finset.mem_erase.mp (hTsubErase hx)).2
  have hownerS : owner ∉ S := fun h =>
    (Finset.mem_erase.mp (hSsubErase h)).1 rfl
  have hownerT : owner ∉ T := fun h =>
    (Finset.mem_erase.mp (hTsubErase h)).1 rfl
  have hScardLt : S.card < O.card := by
    have hproper : S ⊂ O := Finset.ssubset_iff_subset_ne.mpr ⟨hSsub, by
      intro hSO
      exact hownerS (hSO ▸ hownerO)⟩
    exact Finset.card_lt_card hproper
  have hTcardLt : T.card < O.card := by
    have hproper : T ⊂ O := Finset.ssubset_iff_subset_ne.mpr ⟨hTsub, by
      intro hTO
      exact hownerT (hTO ▸ hownerO)⟩
    exact Finset.card_lt_card hproper
  have hSmeet := exceptional_inter_nonempty_of_connected_and_erase_owner_closed
    D O S E owner hconnected hSnonempty hScardLt hSsub hSclosed hownerAdj
  have hTmeet := exceptional_inter_nonempty_of_connected_and_erase_owner_closed
    D O T E owner hconnected hTnonempty hTcardLt hTsub hTclosed hownerAdj
  have hSboundary := sum_boundary_eq_card_exceptional_of_erase_owner_closed
    D O E S owner hownerS hSsub hneighborsO hSclosed hownerAdj
  have hTboundary := sum_boundary_eq_card_exceptional_of_erase_owner_closed
    D O E T owner hownerT hTsub hneighborsO hTclosed hownerAdj
  exact ⟨S, T, hSnonempty, hTnonempty, hunion, hdisj,
    hSclosed, hTclosed, hSmeet, hTmeet, hSboundary, hTboundary⟩

end

end Erdos85

#print axioms Erdos85.exists_deletedOwner_complementary_shores_with_exact_boundaries
