import Proofs.Erdos85OneHighPairingRefinement

/-! # Compact parity states of pairing refinements -/

namespace Erdos85

/-- A distinct bit for each canonical label pair. -/
def oneHighLabelPairBit (pair : OneHighLabelPair) : Nat :=
  1 <<< oneHighLabelPairCode pair

/-- Parity mask of the pairs chosen in one source branch. -/
def oneHighSourcePairingParityMask : List OneHighLabelPair → Nat
  | [] => 0
  | pair :: pairs =>
      oneHighLabelPairBit pair ^^^ oneHighSourcePairingParityMask pairs

/-- Parity mask of the global multiplicities carried by a refinement. -/
def oneHighPairingRefinementParityMask :
    List (List OneHighLabelPair) → Nat
  | [] => 0
  | pairs :: refinement =>
      oneHighSourcePairingParityMask pairs ^^^
        oneHighPairingRefinementParityMask refinement

/-- Reachable global parity masks, deduplicated after every source choice.
Unlike `oneHighChooseEach`, this never materializes duplicate refinement
prefixes that induce the same parity state. -/
def oneHighChooseEachParityStates :
    List (List (List OneHighLabelPair)) → List Nat
  | [] => [0]
  | choices :: remaining =>
      (choices.flatMap fun choice =>
        (oneHighChooseEachParityStates remaining).map fun suffixMask =>
          oneHighSourcePairingParityMask choice ^^^ suffixMask).eraseDups

/-- Compact parity-state image of all compatible pairings of a miss table. -/
def oneHighPairingParityStates
    (profile : Nat) (table : OneHighMissTable) : List Nat :=
  oneHighChooseEachParityStates
    (List.ofFn fun source : Fin 8 =>
      oneHighCompatibleSourcePairings profile table source)

@[simp] theorem oneHighChooseEachParityStates_nil :
    oneHighChooseEachParityStates [] = [0] := rfl

/-- The compact state fold has exactly the same membership semantics as
mapping the parity mask over the full Cartesian refinement enumeration. -/
theorem mem_oneHighChooseEachParityStates_iff
    (choiceLists : List (List (List OneHighLabelPair))) (mask : Nat) :
    mask ∈ oneHighChooseEachParityStates choiceLists ↔
      ∃ refinement ∈ oneHighChooseEach choiceLists,
        oneHighPairingRefinementParityMask refinement = mask := by
  induction choiceLists generalizing mask with
  | nil =>
      simp only [oneHighChooseEachParityStates, List.mem_singleton,
        oneHighChooseEach, exists_eq_left, oneHighPairingRefinementParityMask]
      exact eq_comm
  | cons choices remaining ih =>
      simp only [oneHighChooseEachParityStates, List.mem_eraseDups,
        List.mem_flatMap, List.mem_map, ih]
      constructor
      · rintro ⟨choice, hchoice, suffixMask,
          ⟨refinement, hrefinement, hmask⟩, rfl⟩
        refine ⟨choice :: refinement, ?_, ?_⟩
        · simp [oneHighChooseEach, hchoice, hrefinement]
        · simp [oneHighPairingRefinementParityMask, hmask]
      · rintro ⟨refinement, hrefinement, rfl⟩
        simp only [oneHighChooseEach, List.mem_flatMap,
          List.mem_map] at hrefinement
        rcases hrefinement with
          ⟨choice, hchoice, suffix, hsuffix, rfl⟩
        refine ⟨choice, hchoice,
          oneHighPairingRefinementParityMask suffix, ?_, ?_⟩
        · exact ⟨suffix, hsuffix, rfl⟩
        · rfl

/-- Table-level specialization of the exact parity-image theorem. -/
theorem mem_oneHighPairingParityStates_iff
    (profile : Nat) (table : OneHighMissTable) (mask : Nat) :
    mask ∈ oneHighPairingParityStates profile table ↔
      ∃ refinement ∈ oneHighPairingRefinements profile table,
        oneHighPairingRefinementParityMask refinement = mask := by
  exact mem_oneHighChooseEachParityStates_iff _ _

end Erdos85
