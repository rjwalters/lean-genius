import Proofs.Erdos85OneHighPairingParityReflection

/-! # Explicit parity-mask witnesses for uncovered pairing sectors -/

namespace Erdos85

/-- Fast residual predicate: some reachable compatible-pairing mask avoids
both the odd mate-key and odd cross-`K₂,₂` sectors. -/
def oneHighTableHasPairingParityResidual
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  (oneHighPairingParityStates profile table).any fun mask =>
    !oneHighParityMaskHasMateOrAlternatingSector mask

theorem oneHighTableHasPairingParityResidual_iff
    (profile : Nat) (table : OneHighMissTable) :
    oneHighTableHasPairingParityResidual profile table = true ↔
      ∃ mask ∈ oneHighPairingParityStates profile table,
        oneHighParityMaskHasMateOrAlternatingSector mask = false := by
  simp [oneHighTableHasPairingParityResidual]

/-- The compact residual predicate is exactly the original existential
residual over full compatible refinements. -/
theorem oneHighTableHasPairingParityResidual_eq
    (profile : Nat) (table : OneHighMissTable) :
    oneHighTableHasPairingParityResidual profile table =
      oneHighTableHasPairingSectorResidual profile table := by
  apply Bool.eq_iff_iff.mpr
  rw [oneHighTableHasPairingParityResidual_iff,
    oneHighTableHasPairingSectorResidual_iff]
  constructor
  · rintro ⟨mask, hmask, hsector⟩
    obtain ⟨refinement, hrefinement, rfl⟩ :=
      (mem_oneHighPairingParityStates_iff profile table mask).1 hmask
    refine ⟨refinement, hrefinement, ?_⟩
    rw [← oneHighParityMask_sector_refinement]
    exact hsector
  · rintro ⟨refinement, hrefinement, hsector⟩
    refine ⟨oneHighPairingRefinementParityMask refinement,
      (mem_oneHighPairingParityStates_iff profile table _).2
        ⟨refinement, hrefinement, rfl⟩, ?_⟩
    rw [oneHighParityMask_sector_refinement]
    exact hsector

/-- Every mate-key bit is even in a residual parity mask. -/
theorem oneHighParityMask_mate_even_of_residual
    {mask : Nat}
    (h : oneHighParityMaskHasMateOrAlternatingSector mask = false)
    (i : Fin 4) :
    oneHighParityMaskOdd mask
      (oneHighStandardPairLow i) (oneHighStandardPairHigh i) = false := by
  have hparts : oneHighParityMaskHasOddMateKey mask = false ∧
      oneHighParityMaskHasOddCrossBlock mask = false := by
    simpa [oneHighParityMaskHasMateOrAlternatingSector] using h
  have hmate := hparts.1
  have hn := (List.any_eq_false.mp hmate) i
    ((List.mem_ofFn).2 ⟨i, rfl⟩)
  exact Bool.eq_false_of_not_eq_true hn

/-- Between every two distinct root mate-pairs, a residual mask has at least
one even cross key: the conjunction of all four odd cross bits is false. -/
theorem oneHighParityMask_cross_gap_of_residual
    {mask : Nat}
    (h : oneHighParityMaskHasMateOrAlternatingSector mask = false)
    (i j : Fin 4) (hij : i < j) :
    (oneHighParityMaskOdd mask
        (oneHighStandardPairLow i) (oneHighStandardPairLow j) &&
      oneHighParityMaskOdd mask
        (oneHighStandardPairLow i) (oneHighStandardPairHigh j) &&
      oneHighParityMaskOdd mask
        (oneHighStandardPairHigh i) (oneHighStandardPairLow j) &&
      oneHighParityMaskOdd mask
        (oneHighStandardPairHigh i) (oneHighStandardPairHigh j)) ≠ true := by
  have hparts : oneHighParityMaskHasOddMateKey mask = false ∧
      oneHighParityMaskHasOddCrossBlock mask = false := by
    simpa [oneHighParityMaskHasMateOrAlternatingSector] using h
  have hcross := hparts.2
  have hiNot := (List.any_eq_false.mp hcross) i
    ((List.mem_ofFn).2 ⟨i, rfl⟩)
  have hiFalse :
      ((List.ofFn fun j : Fin 4 => j).any fun j =>
        decide (i < j) &&
        oneHighParityMaskOdd mask
          (oneHighStandardPairLow i) (oneHighStandardPairLow j) &&
        oneHighParityMaskOdd mask
          (oneHighStandardPairLow i) (oneHighStandardPairHigh j) &&
        oneHighParityMaskOdd mask
          (oneHighStandardPairHigh i) (oneHighStandardPairLow j) &&
        oneHighParityMaskOdd mask
          (oneHighStandardPairHigh i) (oneHighStandardPairHigh j)) = false :=
    Bool.eq_false_of_not_eq_true hiNot
  have hjNot := (List.any_eq_false.mp hiFalse) j
    ((List.mem_ofFn).2 ⟨j, rfl⟩)
  simpa [decide_eq_true hij] using hjNot

end Erdos85
