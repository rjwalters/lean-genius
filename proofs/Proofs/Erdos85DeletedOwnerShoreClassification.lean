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

/-- Pure graph-theoretic specialization.  At an articulation vertex of a
connected finite graph, two complementary component shores after deletion
have positive ambient boundaries whose sum is exactly the degree of the
deleted vertex.  This is the order-free cut budget behind the order-nine
`e_S + e_T` calculation. -/
theorem exists_complementary_shores_boundary_sum_eq_degree_of_erase_not_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (owner : V)
    (hconnected : D.Connected)
    (hpuncturedNonempty : ((Finset.univ : Finset V).erase owner).Nonempty)
    (hnot : ¬ (D.induce
      (↑((Finset.univ : Finset V).erase owner) : Set V)).Connected) :
    ∃ S T : Finset V,
      S.Nonempty ∧ T.Nonempty ∧
      S ∪ T = (Finset.univ : Finset V).erase owner ∧ Disjoint S T ∧
      (∀ x ∈ S, D.neighborFinset x ∩
        ((Finset.univ : Finset V).erase owner) ⊆ S) ∧
      (∀ x ∈ T, D.neighborFinset x ∩
        ((Finset.univ : Finset V).erase owner) ⊆ T) ∧
      0 < (∑ x ∈ S,
        (D.neighborFinset x ∩ (Finset.univ \ S)).card) ∧
      0 < (∑ x ∈ T,
        (D.neighborFinset x ∩ (Finset.univ \ T)).card) ∧
      (∑ x ∈ S,
          (D.neighborFinset x ∩ (Finset.univ \ S)).card) +
        (∑ x ∈ T,
          (D.neighborFinset x ∩ (Finset.univ \ T)).card) = D.degree owner := by
  classical
  let E := D.neighborFinset owner
  have hownerAdj : ∀ u ∈ (Finset.univ : Finset V),
      D.Adj u owner ↔ u ∈ E := by
    intro u _
    simp [E, SimpleGraph.mem_neighborFinset, D.adj_comm]
  obtain ⟨S, T, hSnonempty, hTnonempty, hunion, hdisj,
      hSclosed, hTclosed, hSmeet, hTmeet, hSboundary, hTboundary⟩ :=
    exists_deletedOwner_complementary_shores_with_exact_boundaries
      D Finset.univ E owner (Finset.mem_univ owner)
      (by intro u _; exact Finset.subset_univ _)
      hownerAdj (by
        have hc : (D.induce Set.univ).Connected :=
          (D.induceUnivIso.connected_iff).2 hconnected
        rw [show (↑(Finset.univ : Finset V) : Set V) = Set.univ by
          ext x
          simp]
        exact hc) hpuncturedNonempty hnot
  have hEsub : E ⊆ (Finset.univ : Finset V).erase owner := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨by
      intro hxo
      subst x
      exact D.loopless.irrefl owner
        ((D.mem_neighborFinset owner owner).mp hx), Finset.mem_univ x⟩
  have hEunion : (E ∩ S) ∪ (E ∩ T) = E := by
    rw [← Finset.inter_union_distrib_left, hunion]
    exact Finset.inter_eq_left.mpr hEsub
  have hEdisj : Disjoint (E ∩ S) (E ∩ T) := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    exact Finset.disjoint_left.mp hdisj
      (Finset.mem_inter.mp hxS).2 (Finset.mem_inter.mp hxT).2
  have hEcard : (E ∩ S).card + (E ∩ T).card = E.card := by
    rw [← Finset.card_union_of_disjoint hEdisj, hEunion]
  refine ⟨S, T, hSnonempty, hTnonempty, hunion, hdisj,
    hSclosed, hTclosed, ?_, ?_, ?_⟩
  · rw [hSboundary]
    exact Finset.card_pos.mpr hSmeet
  · rw [hTboundary]
    exact Finset.card_pos.mpr hTmeet
  · rw [hSboundary, hTboundary, hEcard]
    exact D.card_neighborFinset_eq_degree owner

end

end Erdos85

#print axioms Erdos85.exists_deletedOwner_complementary_shores_with_exact_boundaries
#print axioms Erdos85.exists_complementary_shores_boundary_sum_eq_degree_of_erase_not_connected
