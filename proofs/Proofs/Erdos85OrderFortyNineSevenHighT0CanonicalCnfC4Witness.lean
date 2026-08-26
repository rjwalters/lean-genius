import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfSatisfaction

/-!
# C4 witnesses for the compact canonical H7/T0 clauses

The generated C4 segment forbids the four cross edges between two distinct
endpoints and two distinct witnesses.  This file isolates the graph-theoretic
kernel fact used to satisfy every such clause.
-/

namespace Erdos85

open SimpleGraph

/-- Boolean meaning of one generator edge status under the graph-induced
low-edge valuation. -/
def sevenHighT0CanonicalEdgeStatusValue
    (val : DimacsValuation) : SevenHighT0CanonicalEdgeStatus → Bool
  | .fixedFalse => false
  | .fixedTrue => true
  | .variable id => val id

set_option maxHeartbeats 0 in
theorem sevenHighT0CanonicalLabelPairs_lookup_pairNat (index : Fin 21) :
    sevenHighT0CanonicalLabelPairs[index.1]? =
      some (sevenHighT0CanonicalPairNat index) := by
  revert index
  decide

/-- On two low numeric vertices, the generator's variable status evaluates
to exactly the corresponding canonical graph adjacency. -/
theorem sevenHighT0CanonicalEdgeStatusValue_low_low
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (a b : Fin 49) (ha : 7 ≤ a.1) (hb : 7 ≤ b.1) :
    sevenHighT0CanonicalEdgeStatusValue (sevenHighT0CanonicalEdgeVal H)
        (sevenHighT0CanonicalEdgeStatus a.1 b.1) =
      sevenHighT0CanonicalAdjBool H a b := by
  by_cases hab : a = b
  · subst b
    simp [sevenHighT0CanonicalEdgeStatus,
      sevenHighT0CanonicalEdgeStatusValue,
      sevenHighT0CanonicalAdjBool]
  · rw [sevenHighT0CanonicalEdgeStatus]
    simp only [show a.1 ≠ b.1 from fun h => hab (Fin.ext h), if_false,
      ha, hb, and_self, if_true, sevenHighT0CanonicalEdgeStatusValue]
    exact sevenHighT0CanonicalEdgeVal_edge H a b ha hb hab

/-- The numeric fixed high--low predicate is exactly the canonical semantic
adjacency after transporting `Fin 49` into the H/E/S/P index. -/
theorem sevenHighT0Canonical_high_low_adj_iff_fixed
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (high low : Fin 49) (hhigh : high.1 < 7) (hlow : 7 ≤ low.1) :
    H.Adj (sevenHighT0CanonicalIndexOfFin high)
        (sevenHighT0CanonicalIndexOfFin low) ↔
      sevenHighT0CanonicalHighLowFixed high.1 low.1 = true := by
  rw [sevenHighT0CanonicalIndexOfFin,
    dif_pos hhigh]
  rw [sevenHighT0CanonicalIndexOfFin,
    dif_neg (by omega)]
  by_cases hempty : low.1 < 14
  · rw [dif_pos hempty]
    have hnot := semantics.high_empty ⟨high.1, hhigh⟩
      ⟨low.1 - 7, by omega⟩
    have hn28 : ¬ 28 ≤ low.1 := by omega
    simp [hnot, sevenHighT0CanonicalHighLowFixed,
      show ¬(14 ≤ low.1 ∧ low.1 < 28) by omega,
      hn28]
  · rw [dif_neg hempty]
    by_cases hsingleton : low.1 < 28
    · rw [dif_pos hsingleton]
      rw [semantics.high_singleton]
      rw [show sevenHighT0CanonicalHighLowFixed high.1 low.1 =
          decide (high.1 = (low.1 - 14) / 2) by
        simp [sevenHighT0CanonicalHighLowFixed,
          show 14 ≤ low.1 ∧ low.1 < 28 by omega]]
      simp only [decide_eq_true_eq]
      constructor
      · intro h
        exact congrArg Fin.val h
      · intro h
        exact Fin.ext h
    · rw [dif_neg hsingleton]
      rw [semantics.high_pair]
      let index : Fin 21 := ⟨low.1 - 28, by omega⟩
      rw [show sevenHighT0CanonicalHighLowFixed high.1 low.1 =
          (decide (high.1 = (sevenHighT0CanonicalPairNat index).1) ||
            decide (high.1 = (sevenHighT0CanonicalPairNat index).2)) by
        unfold sevenHighT0CanonicalHighLowFixed
        rw [if_neg (by omega), if_pos (by omega)]
        rw [sevenHighT0CanonicalLabelPairs_lookup_pairNat index]]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (h | h)
        · exact Or.inl (congrArg Fin.val h)
        · exact Or.inr (congrArg Fin.val h)
      · rintro (h | h)
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)

/-- Every numeric edge status--fixed or variable--has exactly its intended
canonical graph value. -/
theorem sevenHighT0CanonicalEdgeStatusValue_eq_adj
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (a b : Fin 49) :
    sevenHighT0CanonicalEdgeStatusValue (sevenHighT0CanonicalEdgeVal H)
        (sevenHighT0CanonicalEdgeStatus a.1 b.1) =
      sevenHighT0CanonicalAdjBool H a b := by
  by_cases hab : a = b
  · subst b
    simp [sevenHighT0CanonicalEdgeStatus,
      sevenHighT0CanonicalEdgeStatusValue,
      sevenHighT0CanonicalAdjBool]
  · have habVal : a.1 ≠ b.1 := fun h => hab (Fin.ext h)
    by_cases ha : 7 ≤ a.1
    · by_cases hb : 7 ≤ b.1
      · exact sevenHighT0CanonicalEdgeStatusValue_low_low H a b ha hb
      · have hbHigh : b.1 < 7 := by omega
        have hiff := sevenHighT0Canonical_high_low_adj_iff_fixed
          H semantics b a hbHigh ha
        by_cases hfixed :
            sevenHighT0CanonicalHighLowFixed b.1 a.1 = true
        · have hadj := hiff.mpr hfixed
          rw [sevenHighT0CanonicalEdgeStatus, if_neg habVal,
            if_neg (by omega), if_neg (by omega), if_pos hbHigh,
            if_pos hfixed]
          simp [sevenHighT0CanonicalEdgeStatusValue,
            sevenHighT0CanonicalAdjBool, hadj.symm]
        · have hnotAdj : ¬ H.Adj
              (sevenHighT0CanonicalIndexOfFin b)
              (sevenHighT0CanonicalIndexOfFin a) :=
            fun hadj => hfixed (hiff.mp hadj)
          rw [sevenHighT0CanonicalEdgeStatus, if_neg habVal,
            if_neg (by omega), if_neg (by omega), if_pos hbHigh,
            if_neg hfixed]
          have hnotAdjSymm : ¬ H.Adj
              (sevenHighT0CanonicalIndexOfFin a)
              (sevenHighT0CanonicalIndexOfFin b) :=
            fun hadj => hnotAdj hadj.symm
          simp [sevenHighT0CanonicalEdgeStatusValue,
            sevenHighT0CanonicalAdjBool, hnotAdjSymm]
    · have haHigh : a.1 < 7 := by omega
      by_cases hb : b.1 < 7
      · have hnotAdj := semantics.high_high
            ⟨a.1, haHigh⟩ ⟨b.1, hb⟩
        have hfixedFalse :
            sevenHighT0CanonicalHighLowFixed a.1 b.1 = false := by
          simp [sevenHighT0CanonicalHighLowFixed,
            show ¬14 ≤ b.1 by omega, show ¬28 ≤ b.1 by omega]
        rw [sevenHighT0CanonicalEdgeStatus, if_neg habVal,
          if_neg (by omega), if_pos haHigh, if_neg (by
            simpa [hfixedFalse])]
        have haIndex : sevenHighT0CanonicalIndexOfFin a =
            Sum.inl ⟨a.1, haHigh⟩ := by
          simp [sevenHighT0CanonicalIndexOfFin, haHigh]
        have hbIndex : sevenHighT0CanonicalIndexOfFin b =
            Sum.inl ⟨b.1, hb⟩ := by
          simp [sevenHighT0CanonicalIndexOfFin, hb]
        simp [sevenHighT0CanonicalEdgeStatusValue,
          sevenHighT0CanonicalAdjBool, haIndex, hbIndex, hnotAdj]
      · have hbLow : 7 ≤ b.1 := by omega
        have hiff := sevenHighT0Canonical_high_low_adj_iff_fixed
          H semantics a b haHigh hbLow
        by_cases hfixed :
            sevenHighT0CanonicalHighLowFixed a.1 b.1 = true
        · have hadj := hiff.mpr hfixed
          rw [sevenHighT0CanonicalEdgeStatus, if_neg habVal,
            if_neg (by omega), if_pos haHigh, if_pos hfixed]
          simp [sevenHighT0CanonicalEdgeStatusValue,
            sevenHighT0CanonicalAdjBool, hadj]
        · have hnotAdj : ¬ H.Adj
              (sevenHighT0CanonicalIndexOfFin a)
              (sevenHighT0CanonicalIndexOfFin b) :=
            fun hadj => hfixed (hiff.mp hadj)
          rw [sevenHighT0CanonicalEdgeStatus, if_neg habVal,
            if_neg (by omega), if_pos haHigh, if_neg hfixed]
          simp [sevenHighT0CanonicalEdgeStatusValue,
            sevenHighT0CanonicalAdjBool, hnotAdj]

/-- In a C4-free graph, two distinct endpoints and two distinct witnesses
cannot carry all four cross adjacencies. -/
theorem sevenHighT0Canonical_fourCross_not_all_adj
    {H : SimpleGraph SevenHighT0CanonicalIndex}
    [DecidableRel H.Adj]
    (hfree : ¬ containsC4 SevenHighT0CanonicalIndex H)
    {left right first second : SevenHighT0CanonicalIndex}
    (hlr : left ≠ right) (hfs : first ≠ second) :
    ¬ (H.Adj left first ∧ H.Adj right first ∧
      H.Adj left second ∧ H.Adj right second) := by
  rintro ⟨hlf, hrf, hls, hrs⟩
  have hle :=
    (not_containsC4_iff_forall_common_le_one H).mp hfree left right hlr
  have hfirst : first ∈ H.neighborFinset left ∩ H.neighborFinset right := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hlf, hrf⟩
  have hsecond : second ∈ H.neighborFinset left ∩ H.neighborFinset right := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hls, hrs⟩
  exact hfs (Finset.card_le_one.mp hle first hfirst second hsecond)

/-- Clause-shaped disjunctive form: at least one of the four cross edges is
absent. -/
theorem sevenHighT0Canonical_exists_missing_cross_edge
    {H : SimpleGraph SevenHighT0CanonicalIndex}
    [DecidableRel H.Adj]
    (hfree : ¬ containsC4 SevenHighT0CanonicalIndex H)
    {left right first second : SevenHighT0CanonicalIndex}
    (hlr : left ≠ right) (hfs : first ≠ second) :
    ¬ H.Adj left first ∨ ¬ H.Adj right first ∨
      ¬ H.Adj left second ∨ ¬ H.Adj right second := by
  by_contra hall
  simp only [not_or, not_not] at hall
  exact sevenHighT0Canonical_fourCross_not_all_adj hfree hlr hfs
    ⟨hall.1, hall.2.1, hall.2.2.1, hall.2.2.2⟩

/-- The semantic completion package supplies the same clause witness. -/
theorem SevenHighT0CanonicalCompletionSemantics.exists_missing_cross_edge
    {H : SimpleGraph SevenHighT0CanonicalIndex}
    [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    {left right first second : SevenHighT0CanonicalIndex}
    (hlr : left ≠ right) (hfs : first ≠ second) :
    ¬ H.Adj left first ∨ ¬ H.Adj right first ∨
      ¬ H.Adj left second ∨ ¬ H.Adj right second :=
  sevenHighT0Canonical_exists_missing_cross_edge
    semantics.c4Free hlr hfs

end Erdos85

#print axioms Erdos85.sevenHighT0Canonical_fourCross_not_all_adj
#print axioms Erdos85.sevenHighT0CanonicalEdgeStatusValue_low_low
#print axioms Erdos85.sevenHighT0CanonicalEdgeStatusValue_eq_adj
#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.exists_missing_cross_edge
