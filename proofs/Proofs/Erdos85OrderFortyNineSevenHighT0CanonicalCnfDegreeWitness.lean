import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfSatisfaction

/-!
# Sequential-counter witnesses for the canonical H7/T0 degree blocks

This module is separated from the finite indexing bridge so that edits to the
counter construction reuse its compiled standard-kernel proofs.
-/

namespace Erdos85

@[simp] theorem sevenHighT0CanonicalDegreeVars_size (center : Fin 42) :
    (sevenHighT0CanonicalDegreeVars center).size = 41 := by
  simp [sevenHighT0CanonicalDegreeVars]

theorem sevenHighT0CanonicalDegreeVars_getD
    (center : Fin 42) (i : Nat) (hi : i < 41) :
    (sevenHighT0CanonicalDegreeVars center).getD i 0 =
      (sevenHighT0CanonicalLowEdgeId (center.1 + 7)
        ((sevenHighT0CanonicalOtherLow center ⟨i, hi⟩).1 + 7) : Nat) := by
  simp [sevenHighT0CanonicalDegreeVars, Array.getD, hi]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sevenHighT0CanonicalDegreeVarId_bounds
    (center : Fin 42) (index : Fin 41) :
    0 < sevenHighT0CanonicalLowEdgeId (center.1 + 7)
      ((sevenHighT0CanonicalOtherLow center index).1 + 7) ∧
    sevenHighT0CanonicalLowEdgeId (center.1 + 7)
      ((sevenHighT0CanonicalOtherLow center index).1 + 7) ≤ 861 := by
  revert center index
  decide

theorem sevenHighT0CanonicalDegreeInputReifies
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (center : Fin 42) :
    SeqCounterInputReifies (sevenHighT0CanonicalEdgeVal H) 861
      (sevenHighT0CanonicalDegreeVars center)
      (sevenHighT0CanonicalDegreeRow H center) := by
  constructor
  · exact sevenHighT0CanonicalDegreeVars_size center
  · intro i hi
    rw [sevenHighT0CanonicalDegreeVars_getD center i hi]
    exact Int.ofNat_ne_zero.mpr
      (sevenHighT0CanonicalDegreeVarId_bounds center ⟨i, hi⟩).1.ne'
  · intro i hi
    rw [sevenHighT0CanonicalDegreeVars_getD center i hi]
    simpa using (sevenHighT0CanonicalDegreeVarId_bounds center ⟨i, hi⟩).2
  · intro i hi
    rw [sevenHighT0CanonicalDegreeVars_getD center i hi]
    rw [dimacsLitValue_natCast _
      (sevenHighT0CanonicalDegreeVarId_bounds center ⟨i, hi⟩).1]
    let other := sevenHighT0CanonicalOtherLow center ⟨i, hi⟩
    let a : Fin 49 := ⟨center.1 + 7, by omega⟩
    let b : Fin 49 := ⟨other.1 + 7, by omega⟩
    have hne : a ≠ b := by
      intro h
      have hv := congrArg Fin.val h
      apply sevenHighT0CanonicalOtherLow_ne center ⟨i, hi⟩
      apply Fin.ext
      dsimp [a, b, other] at hv ⊢
      omega
    have hedge := sevenHighT0CanonicalEdgeVal_edge H a b
      (by simp [a]) (by simp [b]) hne
    change sevenHighT0CanonicalEdgeVal H
        (sevenHighT0CanonicalLowEdgeId a.1 b.1) = _
    rw [hedge]
    simp [sevenHighT0CanonicalAdjBool, sevenHighT0CanonicalDegreeRow,
      a, b, other, sevenHighT0CanonicalIndexOfFin_low]

set_option maxHeartbeats 0 in
theorem sevenHighT0CanonicalLowSupport_target (center : Fin 42) :
    7 - sevenHighT0LowIndexSupportCard
        (sevenHighT0CanonicalLowIndexOfFin center) =
      sevenHighT0CanonicalLowDegree (center.1 + 7) := by
  revert center
  decide

theorem sevenHighT0CanonicalDegreeRow_target
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (center : Fin 42) :
    seqPrefixTrue (sevenHighT0CanonicalDegreeRow H center) 41 =
      sevenHighT0CanonicalLowDegree (center.1 + 7) := by
  rw [sevenHighT0CanonicalDegreeRow_count]
  have hdegree := sevenHighT0CanonicalNumericLowGraph_degree
    H semantics center
  rw [← sevenHighT0CanonicalLowSupport_target center]
  omega

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalDegreeVarId_bounds
#print axioms Erdos85.sevenHighT0CanonicalDegreeInputReifies
#print axioms Erdos85.sevenHighT0CanonicalDegreeRow_target
