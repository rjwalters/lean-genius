import Proofs.Erdos85OneHighPairingSectorInventory

/-! # Logical reflection of pairing-sensitive parity sectors -/

namespace Erdos85

private theorem ofFn_id_any_eq_true_iff {n : Nat} (p : Fin n → Bool) :
    (List.ofFn fun i : Fin n ↦ i).any p = true ↔
      ∃ i : Fin n, p i = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, hi, hp⟩
    rw [List.mem_ofFn] at hi
    obtain ⟨j, rfl⟩ := hi
    exact ⟨j, hp⟩
  · rintro ⟨i, hp⟩
    refine ⟨i, ?_, hp⟩
    rw [List.mem_ofFn]
    exact ⟨i, rfl⟩

theorem oneHighMultiplicityOdd_eq_true_iff
    (refinement : List (List OneHighLabelPair)) (a b : Fin 8) :
    oneHighMultiplicityOdd refinement a b = true ↔
      Odd (oneHighPairingRefinementMultiplicity refinement
        (oneHighCanonicalLabelPair a b)) := by
  simp [oneHighMultiplicityOdd, Nat.odd_iff]

theorem oneHighRefinementAllOffDiagonalEven_eq_true_iff
    (refinement : List (List OneHighLabelPair)) :
    oneHighRefinementAllOffDiagonalEven refinement = true ↔
      ∀ pair ∈ oneHighCanonicalLabelPairs, pair.1 ≠ pair.2 →
        Even (oneHighPairingRefinementMultiplicity refinement pair) := by
  rw [oneHighRefinementAllOffDiagonalEven, List.all_eq_true]
  constructor
  · intro h pair hpair hne
    have hp := h pair hpair
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hp
    exact Nat.even_iff.mpr (hp.resolve_left hne)
  · intro h pair hpair
    by_cases heq : pair.1 = pair.2
    · simp [heq]
    · simp [heq, Nat.even_iff.mp (h pair hpair heq)]

theorem oneHighRefinementHasOddMateKey_eq_true_iff
    (refinement : List (List OneHighLabelPair)) :
    oneHighRefinementHasOddMateKey refinement = true ↔
      ∃ i : Fin 4,
        Odd (oneHighPairingRefinementMultiplicity refinement
          (oneHighCanonicalLabelPair
            (oneHighStandardPairLow i) (oneHighStandardPairHigh i))) := by
  rw [oneHighRefinementHasOddMateKey, ofFn_id_any_eq_true_iff]
  simp only [oneHighMultiplicityOdd_eq_true_iff]

theorem oneHighRefinementHasOddThreePairTurn_eq_true_iff
    (refinement : List (List OneHighLabelPair)) :
    oneHighRefinementHasOddThreePairTurn refinement = true ↔
      ∃ a b c : Fin 8,
        oneHighLabelPairColor a ≠ oneHighLabelPairColor b ∧
        oneHighLabelPairColor b ≠ oneHighLabelPairColor c ∧
        oneHighLabelPairColor a ≠ oneHighLabelPairColor c ∧
        Odd (oneHighPairingRefinementMultiplicity refinement
          (oneHighCanonicalLabelPair a b)) ∧
        Odd (oneHighPairingRefinementMultiplicity refinement
          (oneHighCanonicalLabelPair b c)) := by
  rw [oneHighRefinementHasOddThreePairTurn, ofFn_id_any_eq_true_iff]
  simp only [ofFn_id_any_eq_true_iff, Bool.and_eq_true,
    decide_eq_true_eq, oneHighMultiplicityOdd_eq_true_iff]
  simp only [and_assoc]

theorem oneHighRefinementHasOddCrossBlock_eq_true_iff
    (refinement : List (List OneHighLabelPair)) :
    oneHighRefinementHasOddCrossBlock refinement = true ↔
      ∃ i j : Fin 4, i < j ∧
        Odd (oneHighPairingRefinementMultiplicity refinement
          (oneHighCanonicalLabelPair
            (oneHighStandardPairLow i) (oneHighStandardPairLow j))) ∧
        Odd (oneHighPairingRefinementMultiplicity refinement
          (oneHighCanonicalLabelPair
            (oneHighStandardPairLow i) (oneHighStandardPairHigh j))) ∧
        Odd (oneHighPairingRefinementMultiplicity refinement
          (oneHighCanonicalLabelPair
            (oneHighStandardPairHigh i) (oneHighStandardPairLow j))) ∧
        Odd (oneHighPairingRefinementMultiplicity refinement
          (oneHighCanonicalLabelPair
            (oneHighStandardPairHigh i) (oneHighStandardPairHigh j))) := by
  rw [oneHighRefinementHasOddCrossBlock, ofFn_id_any_eq_true_iff]
  simp only [ofFn_id_any_eq_true_iff, Bool.and_eq_true,
    decide_eq_true_eq, oneHighMultiplicityOdd_eq_true_iff]
  simp only [and_assoc]

/-- The executable honest classifier returns exactly one of the four Prop-level
sector alternatives needed by the graph consumer. -/
theorem oneHighRefinementHasKnownParitySector_eq_true_iff
    (refinement : List (List OneHighLabelPair)) :
    oneHighRefinementHasKnownParitySector refinement = true ↔
      oneHighRefinementAllOffDiagonalEven refinement = true ∨
      oneHighRefinementHasOddMateKey refinement = true ∨
      oneHighRefinementHasOddThreePairTurn refinement = true ∨
      oneHighRefinementHasOddCrossBlock refinement = true := by
  simp only [oneHighRefinementHasKnownParitySector, Bool.or_eq_true]
  tauto

end Erdos85
