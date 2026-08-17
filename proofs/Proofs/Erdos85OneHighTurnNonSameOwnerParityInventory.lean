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
    sourceAB ≠ sourceBC ∧
    let a := orientedAB.1
    let b := orientedAB.2
    let c := orientedBC.2
    oneHighRootPair a ≠ oneHighRootPair b ∧
    oneHighRootPair b ≠ oneHighRootPair c ∧
    oneHighRootPair a ≠ oneHighRootPair c ∧
    oneHighRootPair sourceAB ≠ oneHighRootPair a ∧
    oneHighRootPair sourceAB ≠ oneHighRootPair b ∧
    oneHighRootPair sourceBC ≠ oneHighRootPair b ∧
    oneHighRootPair sourceBC ≠ oneHighRootPair c ∧
    (sourceAB = oneHighStandardMate sourceBC ∨
     sourceAB = c ∨ sourceAB = oneHighStandardMate c ∨
     sourceBC = a ∨ sourceBC = oneHighStandardMate a))

/-- The odd-pair support encoded by a parity mask has even incidence at each
of the eight labels.  This is the executable Eulerian condition forced by
the even global miss-label fibers of an actual one-high graph. -/
def oneHighParityMaskHasEvenLabelIncidence (mask : Nat) : Bool :=
  (List.ofFn fun label : Fin 8 => label).all fun label =>
    !((List.ofFn fun other : Fin 8 => other).foldl (fun parity other =>
      if other = label then parity
      else parity ^^ oneHighParityMaskOdd mask label other) false)

private theorem foldl_xor_odd_eq_xor_sum_odd
    (values : List Nat) (parity : Bool) :
    values.foldl (fun state value => state ^^ decide (value % 2 = 1)) parity =
      (parity ^^ decide (values.sum % 2 = 1)) := by
  induction values generalizing parity with
  | nil => simp
  | cons value values ih =>
      rw [List.foldl_cons, ih]
      by_cases hp : parity = true <;>
        by_cases hv : value % 2 = 1 <;>
          by_cases hs : values.sum % 2 = 1 <;>
            simp_all [Nat.add_mod]

/-- A concrete refinement whose exact pair multiplicities have even
incidence at every label yields an Eulerian compact parity mask. -/
theorem oneHighParityMaskHasEvenLabelIncidence_refinement
    (refinement : List (List OneHighLabelPair))
    (heven : ∀ label : Fin 8, Even (∑ other : Fin 8,
      if other = label then 0 else
        oneHighPairingRefinementMultiplicity refinement
          (oneHighCanonicalLabelPair label other))) :
    oneHighParityMaskHasEvenLabelIncidence
        (oneHighPairingRefinementParityMask refinement) = true := by
  rw [oneHighParityMaskHasEvenLabelIncidence, List.all_eq_true]
  intro label _
  simp_rw [oneHighParityMaskOdd_refinement, oneHighMultiplicityOdd]
  let values := (List.ofFn fun other : Fin 8 =>
    if other = label then 0 else
      oneHighPairingRefinementMultiplicity refinement
        (oneHighCanonicalLabelPair label other))
  have hfold : (List.ofFn fun other : Fin 8 => other).foldl
      (fun parity other => if other = label then parity else
        parity ^^ decide (oneHighPairingRefinementMultiplicity refinement
          (oneHighCanonicalLabelPair label other) % 2 = 1)) false =
      values.foldl
        (fun parity value => parity ^^ decide (value % 2 = 1)) false := by
    fin_cases label <;> simp [values] <;> rfl
  rw [hfold, foldl_xor_odd_eq_xor_sum_odd]
  simp only [Bool.false_xor]
  have hsum : Even values.sum := by
    simpa [values, List.sum_ofFn, Finset.sum_fin_eq_sum_range,
      Finset.sum_range_succ, add_assoc] using heven label
  have hnot : ¬ values.sum % 2 = 1 := fun hodd =>
    Nat.not_even_iff_odd.mpr (Nat.odd_iff.mpr hodd) hsum
  simp [hnot]

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

/-- Cheap sound abstraction: require the existing odd-turn parity witness and
independently require some reachable Eulerian parity state.  Correlating those
two states can only strengthen this predicate. -/
def oneHighTableHasNonSameOwnerOddTurnAndEulerianState
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  oneHighTableHasNonSameOwnerOddTurnByParity profile table &&
    (oneHighPairingParityStates profile
      (oneHighTableRestrict table)).any oneHighParityMaskHasEvenLabelIncidence

/-- Correlation-preserving variant: the global parity state is recomputed
after fixing the two witnessed owner rows.  Unlike the fast abstraction
above, the oddness tests therefore refer to the same row choices that carry
the two oriented turn edges. -/
def oneHighTableHasNonSameOwnerOddTurnByCorrelatedParity
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  let choices := List.ofFn fun source : Fin 8 =>
    oneHighCompatibleSourcePairings profile (oneHighTableRestrict table) source
  let sources := List.ofFn (fun source : Fin 8 ↦ source)
  sources.any fun sourceAB =>
  sources.any fun sourceBC =>
  choices[sourceAB.val]!.any fun rowAB =>
  choices[sourceBC.val]!.any fun rowBC =>
  let states := oneHighPairingParityStatesWithTwoSourceRowsChoices
    choices sourceAB rowAB sourceBC rowBC
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

def oneHighNonSameOwnerOddTurnAndEulerianStateInventoryTables
    (profile : Fin 5) : List OneHighMissTable :=
  (oneHighCapacityInventoryTables profile).filter
    (oneHighTableHasNonSameOwnerOddTurnAndEulerianState profile.val)

def oneHighNonSameOwnerOddTurnCorrelatedParityInventoryTables
    (profile : Fin 5) : List OneHighMissTable :=
  (oneHighCapacityInventoryTables profile).filter
    (oneHighTableHasNonSameOwnerOddTurnByCorrelatedParity profile.val)

/-- Even after retaining all four graph-forced source-far inequalities, the
sound local-shape/global-parity abstraction accepts the following rows. -/
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

/-- Preserving the correlation between both selected owner rows and the
global parity state still leaves the same five profile counts. -/
theorem oneHighNonSameOwnerOddTurnCorrelatedParityInventory_profile_lengths :
    (List.finRange 5).map (fun profile =>
      (oneHighNonSameOwnerOddTurnCorrelatedParityInventoryTables profile).length) =
      [1333, 3617, 4225, 2693, 650] := by
  native_decide

theorem oneHighNonSameOwnerOddTurnCorrelatedParityInventory_total_length :
    ((List.finRange 5).map fun profile =>
      (oneHighNonSameOwnerOddTurnCorrelatedParityInventoryTables profile).length).sum =
      12518 := by
  rw [oneHighNonSameOwnerOddTurnCorrelatedParityInventory_profile_lengths]
  norm_num

/-- The graph-forced off-diagonal Eulerian parity condition removes no table
from the fast odd-turn inventory.  This negative census rules out that parity
condition alone as the missing one-high obstruction. -/
theorem oneHighNonSameOwnerOddTurnAndEulerianStateInventory_profile_lengths :
    (List.finRange 5).map (fun profile =>
      (oneHighNonSameOwnerOddTurnAndEulerianStateInventoryTables profile).length) =
      [1333, 3617, 4225, 2693, 650] := by
  native_decide

theorem oneHighNonSameOwnerOddTurnAndEulerianStateInventory_total_length :
    ((List.finRange 5).map fun profile =>
      (oneHighNonSameOwnerOddTurnAndEulerianStateInventoryTables profile).length).sum =
      12518 := by
  rw [oneHighNonSameOwnerOddTurnAndEulerianStateInventory_profile_lengths]
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
theorem oneHighTableHasNonSameOwnerOddTurnByBothParities_of_refinement
    {profile : Nat} {table : OneHighMissTable}
    {refinement : List (List OneHighLabelPair)}
    (hrefinement : refinement ∈
      oneHighPairingRefinements profile (oneHighTableRestrict table))
    (hturn : oneHighRefinementHasNonSameOwnerOddTurn refinement = true) :
    oneHighTableHasNonSameOwnerOddTurnByCorrelatedParity profile table = true ∧
      oneHighTableHasNonSameOwnerOddTurnByParity profile table = true := by
  rw [oneHighRefinementHasNonSameOwnerOddTurn] at hturn
  simp only [List.any_eq_true] at hturn
  rcases hturn with ⟨sourceAB, hsourceAB, sourceBC, hsourceBC,
    pairAB, hpairAB, pairBC, hpairBC, orientedAB, horientedAB,
    orientedBC, horientedBC, hshape⟩
  rw [decide_eq_true_eq] at hshape
  rcases hshape with ⟨hjoin, hsourceNe, hab, hbc, hac, hsourceABa, hsourceABb,
    hsourceBCb, hsourceBCc, hoddAB', hoddBC', hrelation⟩
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
    exact hoddAB'
  have hoddBC : oneHighParityMaskOdd
      (oneHighPairingRefinementParityMask refinement)
        orientedBC.1 orientedBC.2 = true := by
    rw [oneHighParityMaskOdd_refinement]
    simpa [hjoin] using hoddBC'
  have hrowABMem' : rowAB ∈ choices[sourceAB.val]! := by
    fin_cases sourceAB <;> simpa [choices] using hrowABMem
  have hrowBCMem' : rowBC ∈ choices[sourceBC.val]! := by
    fin_cases sourceBC <;> simpa [choices] using hrowBCMem
  have hturnShape : oneHighNonSameOwnerOrientedTurnShape
      sourceAB sourceBC orientedAB orientedBC = true := by
    rw [oneHighNonSameOwnerOrientedTurnShape, decide_eq_true_eq]
    exact ⟨hjoin, hsourceNe, hab, hbc, hac, hsourceABa, hsourceABb,
      hsourceBCb, hsourceBCc, hrelation⟩
  constructor
  · have hfixedAB : OneHighChoicesCompatible
        (choices.set sourceAB.val [rowAB]) refinement :=
      oneHighChoicesCompatible_set_singleton_of_getElem?_eq_some
        hcompatible hgetAB
    have hfixedBoth : OneHighChoicesCompatible
        ((choices.set sourceAB.val [rowAB]).set sourceBC.val [rowBC]) refinement :=
      oneHighChoicesCompatible_set_singleton_of_getElem?_eq_some
        hfixedAB hgetBC
    have hfixedMaskMem : oneHighPairingRefinementParityMask refinement ∈
        oneHighPairingParityStatesWithTwoSourceRowsChoices
          choices sourceAB rowAB sourceBC rowBC := by
      rw [oneHighPairingParityStatesWithTwoSourceRowsChoices,
        mem_oneHighChooseEachParityStates_iff]
      exact ⟨refinement, (oneHighChooseEach_mem_iff _ _).2 hfixedBoth, rfl⟩
    rw [oneHighTableHasNonSameOwnerOddTurnByCorrelatedParity]
    simp only [List.any_eq_true, Bool.and_eq_true]
    exact ⟨sourceAB, hsourceAB, sourceBC, hsourceBC,
      rowAB, hrowABMem', rowBC, hrowBCMem',
      pairAB, hpairABRow, pairBC, hpairBCRow,
      orientedAB, horientedAB, orientedBC, horientedBC, hturnShape,
      oneHighPairingRefinementParityMask refinement,
      hfixedMaskMem, hoddAB, hoddBC⟩
  · rw [oneHighTableHasNonSameOwnerOddTurnByParity]
    simp only [List.any_eq_true, Bool.and_eq_true]
    exact ⟨sourceAB, hsourceAB, sourceBC, hsourceBC,
      rowAB, hrowABMem', rowBC, hrowBCMem',
      pairAB, hpairABRow, pairBC, hpairBCRow,
      orientedAB, horientedAB, orientedBC, horientedBC, hturnShape,
      oneHighPairingRefinementParityMask refinement, hmaskMem, hoddAB, hoddBC⟩

theorem oneHighTableHasNonSameOwnerOddTurnByCorrelatedParity_of_refinement
    {profile : Nat} {table : OneHighMissTable}
    {refinement : List (List OneHighLabelPair)}
    (hrefinement : refinement ∈
      oneHighPairingRefinements profile (oneHighTableRestrict table))
    (hturn : oneHighRefinementHasNonSameOwnerOddTurn refinement = true) :
    oneHighTableHasNonSameOwnerOddTurnByCorrelatedParity profile table = true :=
  (oneHighTableHasNonSameOwnerOddTurnByBothParities_of_refinement
    hrefinement hturn).1

theorem oneHighTableHasNonSameOwnerOddTurnByParity_of_refinement
    {profile : Nat} {table : OneHighMissTable}
    {refinement : List (List OneHighLabelPair)}
    (hrefinement : refinement ∈
      oneHighPairingRefinements profile (oneHighTableRestrict table))
    (hturn : oneHighRefinementHasNonSameOwnerOddTurn refinement = true) :
    oneHighTableHasNonSameOwnerOddTurnByParity profile table = true :=
  (oneHighTableHasNonSameOwnerOddTurnByBothParities_of_refinement
    hrefinement hturn).2

/-- Soundness of the proof-friendly Eulerian intersection.  The concrete
refinement supplies both the odd-turn witness and the reachable Eulerian
state, although the executable abstraction deliberately forgets that they
are the same state. -/
theorem oneHighTableHasNonSameOwnerOddTurnAndEulerianState_of_refinement
    {profile : Nat} {table : OneHighMissTable}
    {refinement : List (List OneHighLabelPair)}
    (hrefinement : refinement ∈
      oneHighPairingRefinements profile (oneHighTableRestrict table))
    (hturn : oneHighRefinementHasNonSameOwnerOddTurn refinement = true)
    (heven : ∀ label : Fin 8, Even (∑ other : Fin 8,
      if other = label then 0 else
        oneHighPairingRefinementMultiplicity refinement
          (oneHighCanonicalLabelPair label other))) :
    oneHighTableHasNonSameOwnerOddTurnAndEulerianState profile table = true := by
  rw [oneHighTableHasNonSameOwnerOddTurnAndEulerianState, Bool.and_eq_true]
  refine ⟨oneHighTableHasNonSameOwnerOddTurnByParity_of_refinement
    hrefinement hturn, ?_⟩
  rw [List.any_eq_true]
  refine ⟨oneHighPairingRefinementParityMask refinement, ?_,
    oneHighParityMaskHasEvenLabelIncidence_refinement refinement heven⟩
  exact (mem_oneHighPairingParityStates_iff _ _ _).2
    ⟨refinement, hrefinement, rfl⟩

theorem mem_oneHighNonSameOwnerOddTurnAndEulerianStateInventoryTables_of_refinement
    {profile : Fin 5} {table : OneHighMissTable}
    (hcapacity : table ∈ oneHighCapacityInventoryTables profile)
    {refinement : List (List OneHighLabelPair)}
    (hrefinement : refinement ∈ oneHighPairingRefinements profile.val
      (oneHighTableRestrict table))
    (hturn : oneHighRefinementHasNonSameOwnerOddTurn refinement = true)
    (heven : ∀ label : Fin 8, Even (∑ other : Fin 8,
      if other = label then 0 else
        oneHighPairingRefinementMultiplicity refinement
          (oneHighCanonicalLabelPair label other))) :
    table ∈ oneHighNonSameOwnerOddTurnAndEulerianStateInventoryTables profile := by
  rw [oneHighNonSameOwnerOddTurnAndEulerianStateInventoryTables, List.mem_filter]
  exact ⟨hcapacity,
    oneHighTableHasNonSameOwnerOddTurnAndEulerianState_of_refinement
      hrefinement hturn heven⟩

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
