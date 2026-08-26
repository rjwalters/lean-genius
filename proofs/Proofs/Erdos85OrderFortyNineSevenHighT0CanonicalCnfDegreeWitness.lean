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

theorem List.filter_ne_eq_erase_of_nodup {α : Type} [DecidableEq α]
    (a : α) {xs : List α} (hxs : xs.Nodup) :
    xs.filter (fun x => x ≠ a) = xs.erase a := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.nodup_cons] at hxs
      by_cases hxa : x = a
      · subst x
        simp only [List.erase_cons_head]
        rw [List.filter_cons, if_neg (by simp)]
        apply List.filter_eq_self.mpr
        intro y hy
        simp only [decide_eq_true_eq]
        intro hya
        subst y
        exact hxs.1 hy
      · rw [List.filter_cons, if_pos (by simp [hxa])]
        rw [List.erase_cons_tail (by simpa using hxa)]
        rw [ih hxs.2]

theorem sevenHighT0CanonicalFilteredLowIndices (center : Fin 42) :
    (List.range 42).filter (fun other => other ≠ center.1) =
      List.range center.1 ++ List.range' (center.1 + 1) (41 - center.1) := by
  rw [List.filter_ne_eq_erase_of_nodup center.1 List.nodup_range,
    List.erase_range]
  congr 1
  · rw [Nat.min_eq_right]
    omega
  · rw [show 42 - (center.1 + 1) = 41 - center.1 by omega]

set_option maxHeartbeats 0 in
theorem sevenHighT0CanonicalDegreeVars_eq_generator (center : Fin 42) :
    sevenHighT0CanonicalDegreeVars center =
      ((sevenHighT0CanonicalLows.filter fun other =>
        other ≠ center.1 + 7).toArray.map fun other =>
          (sevenHighT0CanonicalLowEdgeId (center.1 + 7) other : Int)) := by
  have hlow :
      sevenHighT0CanonicalLows.filter (fun other => other ≠ center.1 + 7) =
        (List.range center.1 ++
          List.range' (center.1 + 1) (41 - center.1)).map (fun x => x + 7) := by
    rw [sevenHighT0CanonicalLows, List.filter_map]
    have hpred :
        (List.range 42).filter
            ((fun other => decide (other ≠ center.1 + 7)) ∘ fun x => x + 7) =
          (List.range 42).filter (fun x => x ≠ center.1) := by
      apply List.filter_congr
      intro x hx
      simp
    rw [hpred, sevenHighT0CanonicalFilteredLowIndices]
  rw [hlow]
  apply Array.ext
  · simp [sevenHighT0CanonicalDegreeVars]
    omega
  · intro i hleft hright
    rw [Array.getElem_eq_getD 0,
      sevenHighT0CanonicalDegreeVars_getD center i (by
        simpa using hleft)]
    rw [Array.getElem_map]
    simp only [List.getElem_toArray, List.getElem_map]
    by_cases hi : i < center.1
    · rw [List.getElem_append_left (by simpa using hi), List.getElem_range]
      simp [sevenHighT0CanonicalOtherLow, hi]
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hi),
        List.getElem_range']
      have heq : center.1 + 1 + (i - center.1) + 7 = i + 1 + 7 := by
        omega
      simp only [List.length_range, one_mul]
      rw [heq]
      simp [sevenHighT0CanonicalOtherLow, hi]

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalDegreeVarId_bounds
#print axioms Erdos85.sevenHighT0CanonicalDegreeInputReifies
#print axioms Erdos85.sevenHighT0CanonicalDegreeRow_target
#print axioms Erdos85.sevenHighT0CanonicalDegreeVars_eq_generator
