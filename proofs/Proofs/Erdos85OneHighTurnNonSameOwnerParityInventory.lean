import Proofs.Erdos85OneHighTurnNonSameOwnerInventory
import Proofs.Erdos85OneHighTurnParityReflection

/-! # Parity-state evaluator for non-same-owner turns -/

namespace Erdos85

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Deduplicated parity states after fixing both witnessed owner rows. -/
def oneHighPairingParityStatesWithTwoSourceRowsChoices
    (choices : List (List (List OneHighLabelPair)))
    (sourceAB : Fin 8) (rowAB : List OneHighLabelPair)
    (sourceBC : Fin 8) (rowBC : List OneHighLabelPair) : List Nat :=
  oneHighChooseEachParityStates
    ((choices.set sourceAB.val [rowAB]).set sourceBC.val [rowBC])

def oneHighNonSameOwnerOrientedTurnShape
    (sourceAB sourceBC : Fin 8)
    (orientedAB orientedBC : OneHighLabelPair) : Bool :=
  decide (
    orientedAB.2 = orientedBC.1 ∧
    let a := orientedAB.1
    let b := orientedAB.2
    let c := orientedBC.2
    oneHighRootPair a ≠ oneHighRootPair b ∧
    oneHighRootPair b ≠ oneHighRootPair c ∧
    oneHighRootPair a ≠ oneHighRootPair c ∧
    (sourceAB = oneHighStandardMate sourceBC ∨
     sourceAB = c ∨ sourceAB = oneHighStandardMate c ∨
     sourceBC = a ∨ sourceBC = oneHighStandardMate a))

/-- Table evaluator that never materializes a full pairing refinement.  Local
owner-row shape and globally reachable parity are checked separately; this is
a sound over-approximation of their correlation and is substantially faster
than rebuilding parity states for every fixed row pair. -/
def oneHighTableHasNonSameOwnerOddTurnByParity
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  let choices := List.ofFn fun source : Fin 8 =>
    oneHighCompatibleSourcePairings profile (oneHighTableRestrict table) source
  let sources := List.ofFn (fun source : Fin 8 ↦ source)
  let states := oneHighPairingParityStates profile (oneHighTableRestrict table)
  sources.any fun sourceAB =>
  sources.any fun sourceBC =>
  choices[sourceAB.val]!.any fun rowAB =>
  choices[sourceBC.val]!.any fun rowBC =>
  rowAB.any fun pairAB =>
  rowBC.any fun pairBC =>
  (oneHighLabelPairOrientations pairAB).any fun orientedAB =>
  (oneHighLabelPairOrientations pairBC).any fun orientedBC =>
    oneHighNonSameOwnerOrientedTurnShape
        sourceAB sourceBC orientedAB orientedBC &&
      states.any fun mask =>
          oneHighParityMaskOdd mask orientedAB.1 orientedAB.2 &&
            oneHighParityMaskOdd mask orientedBC.1 orientedBC.2

def oneHighNonSameOwnerOddTurnParityInventoryTables (profile : Fin 5) :
    List OneHighMissTable :=
  (oneHighCapacityInventoryTables profile).filter
    (oneHighTableHasNonSameOwnerOddTurnByParity profile.val)

theorem oneHighNonSameOwnerOddTurnParityInventory_profile_lengths :
    (List.finRange 5).map (fun profile =>
      (oneHighNonSameOwnerOddTurnParityInventoryTables profile).length) =
      [1333, 3617, 4225, 2693, 650] := by
  native_decide

theorem oneHighNonSameOwnerOddTurnParityInventory_total_length :
    ((List.finRange 5).map fun profile =>
      (oneHighNonSameOwnerOddTurnParityInventoryTables profile).length).sum =
      12518 := by
  rw [oneHighNonSameOwnerOddTurnParityInventory_profile_lengths]
  norm_num

private theorem oneHighChoicesCompatible_length_eq {A : Type*}
    {choiceLists : List (List A)} {choices : List A}
    (h : OneHighChoicesCompatible choiceLists choices) :
    choices.length = choiceLists.length := by
  induction choiceLists generalizing choices with
  | nil => cases choices <;> simp [OneHighChoicesCompatible] at h ⊢
  | cons options rest ih =>
      cases choices with
      | nil => simp [OneHighChoicesCompatible] at h
      | cons choice suffix =>
          simp only [OneHighChoicesCompatible] at h
          simp [ih h.2]

/-- Soundness: every exact semantic witness is accepted by the deduplicated
global-parity evaluator. -/
theorem oneHighTableHasNonSameOwnerOddTurnByParity_of_refinement
    {profile : Nat} {table : OneHighMissTable}
    {refinement : List (List OneHighLabelPair)}
    (hrefinement : refinement ∈
      oneHighPairingRefinements profile (oneHighTableRestrict table))
    (hturn : oneHighRefinementHasNonSameOwnerOddTurn refinement = true) :
    oneHighTableHasNonSameOwnerOddTurnByParity profile table = true := by
  rw [oneHighRefinementHasNonSameOwnerOddTurn] at hturn
  simp only [List.any_eq_true] at hturn
  rcases hturn with ⟨sourceAB, hsourceAB, sourceBC, hsourceBC,
    pairAB, hpairAB, pairBC, hpairBC, orientedAB, horientedAB,
    orientedBC, horientedBC, hshape⟩
  rw [decide_eq_true_eq] at hshape
  let choices := List.ofFn fun source : Fin 8 =>
    oneHighCompatibleSourcePairings profile (oneHighTableRestrict table) source
  have hcompatible : OneHighChoicesCompatible choices refinement :=
    (oneHighPairingRefinements_mem_iff profile
      (oneHighTableRestrict table) refinement).1 hrefinement
  have hlen : refinement.length = 8 := by
    simpa [choices] using oneHighChoicesCompatible_length_eq hcompatible
  let rowAB := refinement[sourceAB.val]'(by omega)
  let rowBC := refinement[sourceBC.val]'(by omega)
  have hgetAB : refinement[sourceAB.val]? = some rowAB := by
    rw [List.getElem?_eq_getElem (by omega)]
  have hgetBC : refinement[sourceBC.val]? = some rowBC := by
    rw [List.getElem?_eq_getElem (by omega)]
  have hrowABMem : rowAB ∈ choices[sourceAB.val]! :=
    mem_getElem!_of_oneHighChoicesCompatible_getElem?_eq_some
      hcompatible hgetAB
  have hrowBCMem : rowBC ∈ choices[sourceBC.val]! :=
    mem_getElem!_of_oneHighChoicesCompatible_getElem?_eq_some
      hcompatible hgetBC
  have hpairABRow : pairAB ∈ rowAB := by
    rw [List.getD_eq_getElem?_getD, hgetAB, Option.getD_some] at hpairAB
    exact hpairAB
  have hpairBCRow : pairBC ∈ rowBC := by
    rw [List.getD_eq_getElem?_getD, hgetBC, Option.getD_some] at hpairBC
    exact hpairBC
  have hmaskMem : oneHighPairingRefinementParityMask refinement ∈
      oneHighPairingParityStates profile (oneHighTableRestrict table) := by
    exact (mem_oneHighPairingParityStates_iff _ _ _).2
      ⟨refinement, hrefinement, rfl⟩
  have hoddAB : oneHighParityMaskOdd
      (oneHighPairingRefinementParityMask refinement)
        orientedAB.1 orientedAB.2 = true := by
    rw [oneHighParityMaskOdd_refinement]
    exact hshape.2.2.2.2.1
  have hoddBC : oneHighParityMaskOdd
      (oneHighPairingRefinementParityMask refinement)
        orientedBC.1 orientedBC.2 = true := by
    rw [oneHighParityMaskOdd_refinement]
    simpa [hshape.1] using hshape.2.2.2.2.2.1
  rw [oneHighTableHasNonSameOwnerOddTurnByParity]
  simp only [List.any_eq_true, Bool.and_eq_true]
  refine ⟨sourceAB, hsourceAB, sourceBC, hsourceBC, rowAB, ?_, rowBC, ?_,
    pairAB, hpairABRow, pairBC, hpairBCRow,
    orientedAB, horientedAB, orientedBC, horientedBC, ?_,
    oneHighPairingRefinementParityMask refinement, hmaskMem, hoddAB, hoddBC⟩
  · fin_cases sourceAB <;> simpa [choices] using hrowABMem
  · fin_cases sourceBC <;> simpa [choices] using hrowBCMem
  · rw [oneHighNonSameOwnerOrientedTurnShape, decide_eq_true_eq]
    exact ⟨hshape.1, hshape.2.1, hshape.2.2.1, hshape.2.2.2.1,
      hshape.2.2.2.2.2.2⟩

/-- The semantic inventory is contained in the fast parity inventory. -/
theorem mem_oneHighNonSameOwnerOddTurnParityInventoryTables_of_semantic
    {profile : Fin 5} {table : OneHighMissTable}
    (hmem : table ∈ oneHighNonSameOwnerOddTurnInventoryTables profile) :
    table ∈ oneHighNonSameOwnerOddTurnParityInventoryTables profile := by
  rw [oneHighNonSameOwnerOddTurnInventoryTables, List.mem_filter] at hmem
  rw [oneHighNonSameOwnerOddTurnParityInventoryTables, List.mem_filter]
  refine ⟨hmem.1, ?_⟩
  rw [oneHighTableHasNonSameOwnerOddTurn, List.any_eq_true] at hmem
  obtain ⟨refinement, hrefinement, hturn⟩ := hmem.2
  exact oneHighTableHasNonSameOwnerOddTurnByParity_of_refinement
    hrefinement hturn

/-- Fast-inventory certificate capstone. -/
theorem orderFortyNineStratumExcluded_one_of_parityTurnInventories
    (hall : OneHighAllEvenSectorExcluded)
    (hhexagon : OneHighMateMissHexagonSectorExcluded)
    (hcross : OneHighCrossBlockSectorExcluded)
    (hcheckedSame : ∀ (profile : Fin 5) table,
      table ∈ oneHighSaturatedOddTurnResidualInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (hcheckedOther : ∀ (profile : Fin 5) table,
      table ∈ oneHighNonSameOwnerOddTurnParityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table) :
    OrderFortyNineStratumExcluded 1 := by
  apply orderFortyNineStratumExcluded_one_of_finiteTurnInventories
    hall hhexagon hcross hcheckedSame
  intro profile table hmem
  exact hcheckedOther profile table
    (mem_oneHighNonSameOwnerOddTurnParityInventoryTables_of_semantic hmem)

end Erdos85
