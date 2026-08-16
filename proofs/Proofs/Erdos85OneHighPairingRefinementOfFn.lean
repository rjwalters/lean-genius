import Proofs.Erdos85OneHighPairingRefinement

/-! # Constructing a global pairing refinement from eight local choices -/

namespace Erdos85

/-- Pointwise compatible choices for the eight source branches assemble into
an element of the global Cartesian-product refinement enumeration. -/
theorem oneHigh_listOfFn_mem_pairingRefinements
    (profile : Nat) (table : OneHighMissTable)
    (chosen : Fin 8 → List OneHighLabelPair)
    (hchosen : ∀ source : Fin 8,
      chosen source ∈ oneHighCompatibleSourcePairings profile table source) :
    List.ofFn chosen ∈ oneHighPairingRefinements profile table := by
  rw [oneHighPairingRefinements_mem_iff]
  simp only [List.ofFn_succ, OneHighChoicesCompatible]
  exact ⟨hchosen 0, hchosen 1, hchosen 2, hchosen 3, hchosen 4,
    hchosen 5, hchosen 6, hchosen 7, trivial⟩

/-- Conversely, a refinement presented as `List.ofFn` is globally enumerated
exactly when each of its eight local choices is enumerated. -/
theorem oneHigh_listOfFn_mem_pairingRefinements_iff
    (profile : Nat) (table : OneHighMissTable)
    (chosen : Fin 8 → List OneHighLabelPair) :
    List.ofFn chosen ∈ oneHighPairingRefinements profile table ↔
      ∀ source : Fin 8,
        chosen source ∈
          oneHighCompatibleSourcePairings profile table source := by
  constructor
  · intro href source
    rw [oneHighPairingRefinements_mem_iff] at href
    simp only [List.ofFn_succ, OneHighChoicesCompatible] at href
    fin_cases source <;> simp_all
  · exact oneHigh_listOfFn_mem_pairingRefinements profile table chosen

end Erdos85
