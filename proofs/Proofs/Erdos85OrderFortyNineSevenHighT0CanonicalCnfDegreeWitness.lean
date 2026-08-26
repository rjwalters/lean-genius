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

theorem SeqCounterInputReifies.mono_agree
    {n : Nat} {base next : DimacsValuation} {baseTop nextTop : Nat}
    {vars : Array Int} {x : Fin n → Bool}
    (h : SeqCounterInputReifies base baseTop vars x)
    (htop : baseTop ≤ nextTop)
    (hagree : ∀ id, id ≤ baseTop → next id = base id) :
    SeqCounterInputReifies next nextTop vars x := by
  constructor
  · exact h.size_eq
  · exact h.nonzero
  · intro i hi
    exact (h.bounded i hi).trans htop
  · intro i hi
    rw [← h.value i hi]
    exact dimacsLitValue_eq_of_agree next base
      (hagree _ (h.bounded i hi))

abbrev SevenHighT0CanonicalDegreeValState :=
  SevenHighT0CanonicalCnfState × DimacsValuation

structure SevenHighT0CanonicalDegreeSemanticSound
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (acc : SevenHighT0CanonicalDegreeValState) : Prop where
  top_bound : 861 ≤ acc.1.top
  satisfied : dimacsFormulaSatisfied acc.2 acc.1.clauses
  bounded : dimacsFormulaBounded acc.1.top acc.1.clauses
  edge_agree : ∀ id, id ≤ 861 → acc.2 id = sevenHighT0CanonicalEdgeVal H id

def sevenHighT0CanonicalDegreeVarsRow
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (center : Fin 42) :
    Fin (sevenHighT0CanonicalDegreeVars center).size → Bool := fun index =>
  sevenHighT0CanonicalDegreeRow H center
    (Fin.cast (sevenHighT0CanonicalDegreeVars_size center) index)

theorem sevenHighT0CanonicalDegreeVarsRow_inputReifies
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (center : Fin 42) :
    SeqCounterInputReifies (sevenHighT0CanonicalEdgeVal H) 861
      (sevenHighT0CanonicalDegreeVars center)
      (sevenHighT0CanonicalDegreeVarsRow H center) := by
  let base := sevenHighT0CanonicalDegreeInputReifies H center
  constructor
  · rfl
  · intro i hi
    exact base.nonzero i (by
      rw [← sevenHighT0CanonicalDegreeVars_size center]
      exact hi)
  · intro i hi
    exact base.bounded i (by
      rw [← sevenHighT0CanonicalDegreeVars_size center]
      exact hi)
  · intro i hi
    have hi' : i < 41 := by
      rw [← sevenHighT0CanonicalDegreeVars_size center]
      exact hi
    simpa only [sevenHighT0CanonicalDegreeVarsRow, Fin.cast_mk] using
      base.value i hi'

theorem sevenHighT0CanonicalDegreeVarsRow_target
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (center : Fin 42) :
    seqPrefixTrue (sevenHighT0CanonicalDegreeVarsRow H center)
        (sevenHighT0CanonicalDegreeVars center).size =
      sevenHighT0CanonicalLowDegree (center.1 + 7) := by
  calc
    _ = seqPrefixTrue (sevenHighT0CanonicalDegreeVarsRow H center) 41 :=
      congrArg (seqPrefixTrue (sevenHighT0CanonicalDegreeVarsRow H center))
        (sevenHighT0CanonicalDegreeVars_size center)
    _ = seqPrefixTrue (sevenHighT0CanonicalDegreeRow H center) 41 := by
      unfold seqPrefixTrue
      apply congrArg Finset.card
      ext i
      by_cases hi : i < 41
      · simp [hi, sevenHighT0CanonicalDegreeVarsRow]
      · simp [hi]
    _ = _ := sevenHighT0CanonicalDegreeRow_target H semantics center

def sevenHighT0CanonicalDegreeStepVal
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (center : Fin 42) (acc : SevenHighT0CanonicalDegreeValState) :
    SevenHighT0CanonicalDegreeValState :=
  let vars := sevenHighT0CanonicalDegreeVars center
  let target := sevenHighT0CanonicalLowDegree (center.1 + 7)
  let out := seqCounterEquals acc.1.top vars target
  ({ top := out.top, clauses := acc.1.clauses ++ out.clauses },
    seqCounterEqualsVal acc.2 acc.1.top vars
      (sevenHighT0CanonicalDegreeVarsRow H center) target)

@[simp] theorem sevenHighT0CanonicalDegreeStepVal_state
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (center : Fin 42) (acc : SevenHighT0CanonicalDegreeValState) :
    (sevenHighT0CanonicalDegreeStepVal H center acc).1 =
      sevenHighT0CanonicalDegreeStep (center.1 + 7) acc.1 := by
  rw [sevenHighT0CanonicalDegreeStep]
  rw [← sevenHighT0CanonicalDegreeVars_eq_generator center]
  rfl

theorem sevenHighT0CanonicalDegreeSemanticSound_initial
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    SevenHighT0CanonicalDegreeSemanticSound H
      (({} : SevenHighT0CanonicalCnfState), sevenHighT0CanonicalEdgeVal H) := by
  constructor
  · rfl
  · exact dimacsFormulaSatisfied_empty _
  · exact dimacsFormulaBounded_empty _
  · intros
    rfl

theorem sevenHighT0CanonicalDegreeStepVal_semanticSound
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (center : Fin 42) {acc : SevenHighT0CanonicalDegreeValState}
    (h : SevenHighT0CanonicalDegreeSemanticSound H acc) :
    SevenHighT0CanonicalDegreeSemanticSound H
      (sevenHighT0CanonicalDegreeStepVal H center acc) := by
  let vars := sevenHighT0CanonicalDegreeVars center
  let row := sevenHighT0CanonicalDegreeVarsRow H center
  let target := sevenHighT0CanonicalLowDegree (center.1 + 7)
  have hinput : SeqCounterInputReifies acc.2 acc.1.top vars row :=
    (sevenHighT0CanonicalDegreeVarsRow_inputReifies H center).mono_agree
      h.top_bound h.edge_agree
  have hblock := seqCounterEqualsVal_formulaSatisfied_append
    acc.2 acc.1.top acc.1.clauses vars row h.satisfied h.bounded
      hinput target (sevenHighT0CanonicalDegreeVarsRow_target H semantics center)
  constructor
  · exact h.top_bound.trans (seqCounterEquals_top_bound acc.1.top vars target)
  · exact hblock.1
  · exact hblock.2.1
  · intro id hid
    exact (seqCounterEqualsVal_input acc.2 acc.1.top vars row target id
      (hid.trans h.top_bound)).trans (h.edge_agree id hid)

def sevenHighT0CanonicalDegreeNatStepVal
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (center : Nat) (acc : SevenHighT0CanonicalDegreeValState) :
    SevenHighT0CanonicalDegreeValState :=
  if hc : center < 42 then
    sevenHighT0CanonicalDegreeStepVal H ⟨center, hc⟩ acc
  else acc

def sevenHighT0CanonicalDegreeStateVal
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    SevenHighT0CanonicalDegreeValState :=
  (List.range 42).foldl
    (fun acc center => sevenHighT0CanonicalDegreeNatStepVal H center acc)
    (({} : SevenHighT0CanonicalCnfState), sevenHighT0CanonicalEdgeVal H)

theorem sevenHighT0CanonicalDegreeNatStepVal_semanticSound
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (center : Nat) {acc : SevenHighT0CanonicalDegreeValState}
    (h : SevenHighT0CanonicalDegreeSemanticSound H acc) :
    SevenHighT0CanonicalDegreeSemanticSound H
      (sevenHighT0CanonicalDegreeNatStepVal H center acc) := by
  by_cases hc : center < 42
  · simpa [sevenHighT0CanonicalDegreeNatStepVal, hc] using
      sevenHighT0CanonicalDegreeStepVal_semanticSound
        H semantics ⟨center, hc⟩ h
  · simpa [sevenHighT0CanonicalDegreeNatStepVal, hc] using h

theorem sevenHighT0CanonicalDegreeFoldVal_semanticSound
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H)
    (centers : List Nat) {acc : SevenHighT0CanonicalDegreeValState}
    (h : SevenHighT0CanonicalDegreeSemanticSound H acc) :
    SevenHighT0CanonicalDegreeSemanticSound H
      (centers.foldl
        (fun acc center => sevenHighT0CanonicalDegreeNatStepVal H center acc)
        acc) := by
  induction centers generalizing acc with
  | nil => exact h
  | cons center centers ih =>
      exact ih (sevenHighT0CanonicalDegreeNatStepVal_semanticSound
        H semantics center h)

theorem sevenHighT0CanonicalDegreeStateVal_semanticSound
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    SevenHighT0CanonicalDegreeSemanticSound H
      (sevenHighT0CanonicalDegreeStateVal H) := by
  exact sevenHighT0CanonicalDegreeFoldVal_semanticSound H semantics _
    (sevenHighT0CanonicalDegreeSemanticSound_initial H)

theorem sevenHighT0CanonicalDegreeFoldVal_state
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (centers : List Nat) (hcenters : ∀ center ∈ centers, center < 42)
    (acc : SevenHighT0CanonicalDegreeValState) :
    (centers.foldl
        (fun acc center => sevenHighT0CanonicalDegreeNatStepVal H center acc)
        acc).1 =
      centers.foldl
        (fun st center => sevenHighT0CanonicalDegreeStep (center + 7) st)
        acc.1 := by
  induction centers generalizing acc with
  | nil => rfl
  | cons center centers ih =>
      simp only [List.foldl_cons]
      rw [ih (fun candidate hmem => hcenters candidate (List.mem_cons_of_mem _ hmem))]
      have hc := hcenters center (by simp)
      simp [sevenHighT0CanonicalDegreeNatStepVal, hc]

@[simp] theorem sevenHighT0CanonicalDegreeStateVal_state
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj] :
    (sevenHighT0CanonicalDegreeStateVal H).1 =
      sevenHighT0CanonicalDegreeState := by
  rw [sevenHighT0CanonicalDegreeStateVal,
    sevenHighT0CanonicalDegreeFoldVal_state H (List.range 42) (by simp)]
  rw [sevenHighT0CanonicalDegreeState, sevenHighT0CanonicalLows,
    List.foldl_map]

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalDegreeVarId_bounds
#print axioms Erdos85.sevenHighT0CanonicalDegreeInputReifies
#print axioms Erdos85.sevenHighT0CanonicalDegreeRow_target
#print axioms Erdos85.sevenHighT0CanonicalDegreeVars_eq_generator
#print axioms Erdos85.sevenHighT0CanonicalDegreeStepVal_semanticSound
#print axioms Erdos85.sevenHighT0CanonicalDegreeStateVal_semanticSound
