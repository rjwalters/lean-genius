import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalSemanticEmptyMask
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyOrbitWitness

/-! # Semantic admissibility of the canonical empty-sector mask -/

namespace Erdos85

open SimpleGraph

theorem sevenHighT0CanonicalEmptySemanticDegree_eq
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (vertex : Fin 7) :
    sevenHighT0CanonicalEmptyDegree
        (sevenHighT0CanonicalEmptySemanticMask H) vertex.1 =
      (H.comap (fun w : Fin 7 => Sum.inr (Sum.inl w))).degree vertex := by
  let E := H.comap (fun w : Fin 7 => Sum.inr (Sum.inl w))
  rw [← E.card_neighborFinset_eq_degree]
  have hadj : ∀ other : Fin 7,
      sevenHighT0CanonicalEmptyAdj
          (sevenHighT0CanonicalEmptySemanticMask H) vertex.1 other.1 =
        decide (E.Adj vertex other) := by
    intro other
    exact sevenHighT0CanonicalEmptySemanticMaskAdj_eq H vertex other
  rw [sevenHighT0CanonicalEmptyDegree,
    ← List.map_coe_finRange_eq_range, List.countP_map]
  change (List.finRange 7).countP (fun other =>
      sevenHighT0CanonicalEmptyAdj
        (sevenHighT0CanonicalEmptySemanticMask H) vertex.1 other.1) = _
  simp_rw [hadj]
  rw [List.countP_eq_length_filter]
  have hnodup :
      (List.filter (fun other => decide (E.Adj vertex other))
        (List.finRange 7)).Nodup :=
    List.Nodup.filter _ (List.nodup_finRange 7)
  rw [← List.toFinset_card_of_nodup hnodup,
    List.toFinset_filter]
  congr 1
  ext other
  simp [E]

set_option maxHeartbeats 1000000 in
private theorem finGraph_inducedEmptyFiber_degree_eq
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (y : {i : Fin 49 // i ∈ sevenHighT0LowSupportFiber G 0}) :
    (G.induce (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))).degree y =
      sevenHighT0LowEmptyNeighborCount G y.1 := by
  rw [← (G.induce
    (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))).card_neighborFinset_eq_degree]
  calc
    _ = (((G.induce
          (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))).neighborFinset y).map
          (Function.Embedding.subtype _)).card := by simp
    _ = (G.neighborFinset y.1 ∩
          (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49)).toFinset).card := by
      congr 1
      ext x
      simp
    _ = sevenHighT0LowEmptyNeighborCount G y.1 := by
      congr 1
      ext
      simp [sevenHighT0LowSupportFiber,
        orderFortyNineLowVertices,
        and_assoc, and_left_comm, and_comm]

theorem SevenHighT0CanonicalCompletionSemantics.semanticEmptyDegree_le_three
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (vertex : Fin 7) :
    sevenHighT0CanonicalEmptyDegree
        (sevenHighT0CanonicalEmptySemanticMask H) vertex.1 ≤ 3 := by
  let G := sevenHighT0CanonicalFinGraph H
  let y := semantics.finGraphEmptyFiberEquiv vertex
  rw [sevenHighT0CanonicalEmptySemanticDegree_eq]
  have hdegreeIso :
      (H.comap (fun w : Fin 7 => Sum.inr (Sum.inl w))).degree vertex =
        (G.induce (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))).degree y := by
    calc
      _ = Fintype.card
          ((H.comap (fun w : Fin 7 => Sum.inr (Sum.inl w))).neighborSet vertex) := by
        rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card]
      _ = Fintype.card
          ((G.induce (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))).neighborSet y) :=
        Fintype.card_congr (semantics.finGraphEmptyFiberIso.mapNeighborSet vertex)
      _ = _ := by
        rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card]
  rw [hdegreeIso, finGraph_inducedEmptyFiber_degree_eq]
  have hy : G.degree y.1 = 7 := by
    rw [sevenHighT0CanonicalFinGraph_degree]
    have hyIndex : sevenHighT0CanonicalIndexEquiv y.1 =
        Sum.inr (Sum.inl vertex) := by
      simp [y, SevenHighT0CanonicalCompletionSemantics.finGraphEmptyFiberEquiv]
    rw [hyIndex]
    exact semantics.low_degree_full (Sum.inl vertex)
  exact semantics.finGraph_emptyRoot_bound hy

theorem sevenHighT0CanonicalEmptySemanticCommonCount_eq
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (left right : Fin 7) :
    sevenHighT0CanonicalEmptyCommonCount
        (sevenHighT0CanonicalEmptySemanticMask H) left.1 right.1 =
      ((H.comap (fun w : Fin 7 => Sum.inr (Sum.inl w))).neighborFinset left ∩
        (H.comap (fun w : Fin 7 => Sum.inr (Sum.inl w))).neighborFinset right).card := by
  let E := H.comap (fun w : Fin 7 => Sum.inr (Sum.inl w))
  have hadj (root other : Fin 7) :
      sevenHighT0CanonicalEmptyAdj
          (sevenHighT0CanonicalEmptySemanticMask H) root.1 other.1 =
        decide (E.Adj root other) :=
    sevenHighT0CanonicalEmptySemanticMaskAdj_eq H root other
  rw [sevenHighT0CanonicalEmptyCommonCount,
    ← List.map_coe_finRange_eq_range, List.countP_map]
  change (List.finRange 7).countP (fun witness =>
      sevenHighT0CanonicalEmptyAdj
          (sevenHighT0CanonicalEmptySemanticMask H) left.1 witness.1 &&
        sevenHighT0CanonicalEmptyAdj
          (sevenHighT0CanonicalEmptySemanticMask H) right.1 witness.1) = _
  simp_rw [hadj]
  rw [List.countP_eq_length_filter]
  have hnodup :
      (List.filter (fun witness =>
          decide (E.Adj left witness) && decide (E.Adj right witness))
        (List.finRange 7)).Nodup :=
    List.Nodup.filter _ (List.nodup_finRange 7)
  rw [← List.toFinset_card_of_nodup hnodup, List.toFinset_filter]
  congr 1
  ext witness
  simp [E]

private theorem canonicalEmptyInduced_not_containsC4
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    ¬ containsC4 (Fin 7)
      (H.comap (fun w : Fin 7 => Sum.inr (Sum.inl w))) := by
  rintro ⟨f, hf, hadj⟩
  apply semantics.c4Free
  refine ⟨fun i => Sum.inr (Sum.inl (f i)), ?_, ?_⟩
  · intro i j hij
    apply hf
    simpa using hij
  · intro i j hij
    exact hadj i j hij

theorem SevenHighT0CanonicalCompletionSemantics.semanticEmptyCommonCount_le_one
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (left right : Fin 7) (hne : left ≠ right) :
    sevenHighT0CanonicalEmptyCommonCount
        (sevenHighT0CanonicalEmptySemanticMask H) left.1 right.1 ≤ 1 := by
  rw [sevenHighT0CanonicalEmptySemanticCommonCount_eq]
  exact common_le_one_of_not_containsC4
    (canonicalEmptyInduced_not_containsC4 semantics) left right hne

theorem SevenHighT0CanonicalCompletionSemantics.semanticEmptyPassesGraphFilters
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    sevenHighT0CanonicalEmptyPassesGraphFilters
        (sevenHighT0CanonicalEmptySemanticMask H) = true := by
  rw [sevenHighT0CanonicalEmptyPassesGraphFilters, Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro vertex hvertex
    have hlt : vertex < 7 := List.mem_range.mp hvertex
    rw [decide_eq_true_eq]
    exact semantics.semanticEmptyDegree_le_three ⟨vertex, hlt⟩
  · rw [List.all_eq_true]
    intro pair hpair
    change pair ∈ (List.range 7).flatMap (fun left =>
      ((List.range 7).filter fun right => left < right).map
        fun right => (left, right)) at hpair
    rw [List.mem_flatMap] at hpair
    obtain ⟨left, hleft, hpair⟩ := hpair
    rw [List.mem_map] at hpair
    obtain ⟨right, hright, rfl⟩ := hpair
    have hrightData := List.mem_filter.mp hright
    have hleftLt : left < 7 := List.mem_range.mp hleft
    have hrightLt : right < 7 := List.mem_range.mp hrightData.1
    have hne : (⟨left, hleftLt⟩ : Fin 7) ≠ ⟨right, hrightLt⟩ := by
      exact ne_of_lt (show (⟨left, hleftLt⟩ : Fin 7) <
        ⟨right, hrightLt⟩ by
          exact of_decide_eq_true hrightData.2)
    rw [decide_eq_true_eq]
    exact semantics.semanticEmptyCommonCount_le_one
      ⟨left, hleftLt⟩ ⟨right, hrightLt⟩ hne

theorem SevenHighT0CanonicalCompletionSemantics.semanticEmptyMask_admissible
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    sevenHighT0CanonicalEmptyAdmissible
        (sevenHighT0CanonicalEmptySemanticMask H) = true := by
  rw [sevenHighT0CanonicalEmptyAdmissible]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hbounds := semantics.semanticMask_edge_bounds
  exact ⟨⟨⟨sevenHighT0CanonicalEmptySemanticMask_lt H,
    hbounds.1⟩, hbounds.2⟩,
    semantics.semanticEmptyPassesGraphFilters⟩

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptySemanticDegree_eq
#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.semanticEmptyDegree_le_three
#print axioms Erdos85.sevenHighT0CanonicalEmptySemanticCommonCount_eq
#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.semanticEmptyMask_admissible
