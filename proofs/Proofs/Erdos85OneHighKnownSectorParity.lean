import Proofs.Erdos85OneHighPairingParityReflection

/-! # Complete known-sector classifier on compact parity masks -/

namespace Erdos85

def oneHighParityMaskAllOffDiagonalEven (mask : Nat) : Bool :=
  oneHighCanonicalLabelPairs.all fun pair =>
    decide (pair.1 = pair.2) ||
      !mask.testBit (oneHighLabelPairCode pair)

def oneHighParityMaskHasOddThreePairTurn (mask : Nat) : Bool :=
  (List.ofFn fun a : Fin 8 => a).any fun a =>
    (List.ofFn fun b : Fin 8 => b).any fun b =>
      (List.ofFn fun c : Fin 8 => c).any fun c =>
        decide (oneHighLabelPairColor a ≠ oneHighLabelPairColor b) &&
        decide (oneHighLabelPairColor b ≠ oneHighLabelPairColor c) &&
        decide (oneHighLabelPairColor a ≠ oneHighLabelPairColor c) &&
        oneHighParityMaskOdd mask a b &&
        oneHighParityMaskOdd mask b c

def oneHighParityMaskHasKnownSector (mask : Nat) : Bool :=
  oneHighParityMaskAllOffDiagonalEven mask ||
    oneHighParityMaskHasOddMateKey mask ||
    oneHighParityMaskHasOddThreePairTurn mask ||
    oneHighParityMaskHasOddCrossBlock mask

private theorem decide_mod_two_zero_eq_not_one (n : Nat) :
    decide (n % 2 = 0) = !decide (n % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem oneHighParityMaskAllOffDiagonalEven_refinement
    (refinement : List (List OneHighLabelPair)) :
    oneHighParityMaskAllOffDiagonalEven
        (oneHighPairingRefinementParityMask refinement) =
      oneHighRefinementAllOffDiagonalEven refinement := by
  unfold oneHighParityMaskAllOffDiagonalEven
    oneHighRefinementAllOffDiagonalEven
  simp_rw [testBit_oneHighPairingRefinementParityMask,
    decide_mod_two_zero_eq_not_one]

theorem oneHighParityMaskHasOddMateKey_refinement
    (refinement : List (List OneHighLabelPair)) :
    oneHighParityMaskHasOddMateKey
        (oneHighPairingRefinementParityMask refinement) =
      oneHighRefinementHasOddMateKey refinement := by
  simp [oneHighParityMaskHasOddMateKey,
    oneHighRefinementHasOddMateKey]

theorem oneHighParityMaskHasOddCrossBlock_refinement
    (refinement : List (List OneHighLabelPair)) :
    oneHighParityMaskHasOddCrossBlock
        (oneHighPairingRefinementParityMask refinement) =
      oneHighRefinementHasOddCrossBlock refinement := by
  simp [oneHighParityMaskHasOddCrossBlock,
    oneHighRefinementHasOddCrossBlock]

theorem oneHighParityMaskHasOddThreePairTurn_refinement
    (refinement : List (List OneHighLabelPair)) :
    oneHighParityMaskHasOddThreePairTurn
        (oneHighPairingRefinementParityMask refinement) =
      oneHighRefinementHasOddThreePairTurn refinement := by
  simp [oneHighParityMaskHasOddThreePairTurn,
    oneHighRefinementHasOddThreePairTurn]

/-- Complete compact classifier reflection. -/
theorem oneHighParityMask_knownSector_refinement
    (refinement : List (List OneHighLabelPair)) :
    oneHighParityMaskHasKnownSector
        (oneHighPairingRefinementParityMask refinement) =
      oneHighRefinementHasKnownParitySector refinement := by
  simp [oneHighParityMaskHasKnownSector,
    oneHighRefinementHasKnownParitySector,
    oneHighParityMaskAllOffDiagonalEven_refinement,
    oneHighParityMaskHasOddMateKey_refinement,
    oneHighParityMaskHasOddThreePairTurn_refinement,
    oneHighParityMaskHasOddCrossBlock_refinement]

def oneHighTableKnownParitySectorsCoveredByParity
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  let states := oneHighPairingParityStates profile table
  !states.isEmpty && states.all oneHighParityMaskHasKnownSector

/-- Universal coverage by the compact complete classifier is exactly the
existing universal coverage predicate over full refinements. -/
theorem oneHighTableKnownParitySectorsCoveredByParity_eq
    (profile : Nat) (table : OneHighMissTable) :
    oneHighTableKnownParitySectorsCoveredByParity profile table =
      oneHighTableKnownParitySectorsCovered profile table := by
  apply Bool.eq_iff_iff.mpr
  simp only [oneHighTableKnownParitySectorsCoveredByParity,
    oneHighTableKnownParitySectorsCovered, Bool.and_eq_true,
    List.all_eq_true]
  constructor
  · rintro ⟨hstates, hall⟩
    constructor
    · have hstatesNe : oneHighPairingParityStates profile table ≠ [] := by
        intro h
        simp [h] at hstates
      have hrefinementsNe :
          oneHighPairingRefinements profile table ≠ [] := by
        intro hrefinements
        apply hstatesNe
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro mask hmask
        obtain ⟨refinement, hrefinement, _⟩ :=
          (mem_oneHighPairingParityStates_iff profile table mask).1 hmask
        rw [hrefinements] at hrefinement
        simp at hrefinement
      cases h : oneHighPairingRefinements profile table with
      | nil => exact (hrefinementsNe h).elim
      | cons head tail => simp
    · intro refinement hrefinement
      rw [← oneHighParityMask_knownSector_refinement]
      apply hall
      exact (mem_oneHighPairingParityStates_iff profile table _).2
        ⟨refinement, hrefinement, rfl⟩
  · rintro ⟨hrefinements, hall⟩
    constructor
    · have hrefinementsNe :
          oneHighPairingRefinements profile table ≠ [] := by
        intro h
        simp [h] at hrefinements
      have hstatesNe : oneHighPairingParityStates profile table ≠ [] := by
        intro hstates
        apply hrefinementsNe
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro refinement hrefinement
        have hm := (mem_oneHighPairingParityStates_iff profile table _).2
          ⟨refinement, hrefinement, rfl⟩
        rw [hstates] at hm
        simp at hm
      cases h : oneHighPairingParityStates profile table with
      | nil => exact (hstatesNe h).elim
      | cons head tail => simp
    · intro mask hmask
      obtain ⟨refinement, hrefinement, rfl⟩ :=
        (mem_oneHighPairingParityStates_iff profile table mask).1 hmask
      rw [oneHighParityMask_knownSector_refinement]
      exact hall refinement hrefinement

end Erdos85
