import Proofs.Erdos85SizeTwoAllowedDifferenceParityCard
import Proofs.Erdos85SizeTwoEigenlineCyclicSharpParityBalance
import Proofs.Erdos85SizeTwoEigenlineCyclicBinaryDefectParity

/-!
# Exact binary parity census for sharp cyclic defects

Node: BinarySizeTwoCyclicPackingBound beneath outline A.5.3.

For 4 dividing q, the forced duplicate-minus-missing displacement crosses
mod-two parity in every sharp row. Reciprocity and the balanced allowed-fiber
partition then force exactly q(q/2-1) rows of each orientation.
-/

namespace Erdos85

noncomputable section

private theorem zmodTwo_eq_zero_iff_other_ne_zero
    (x y : ZMod 2) (hxy : x ≠ y) :
    x = 0 ↔ y ≠ 0 := by
  fin_cases x <;> fin_cases y
  all_goals aesop
  exact (a rfl).elim

/-- Exact orientation census for the binary sharp subsystem. -/
theorem sizeTwoCyclicSharpProfile_binaryDuplicateParity_card
    {q : ℕ} [NeZero q] (h4q : 4 ∣ q) {a : ZMod q}
    [DecidableEq (sizeTwoAllowedDifference q a)]
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (duplicate missing : ZMod q → sizeTwoAllowedDifference q a →
      sizeTwoAllowedDifference q a)
    (hprofile : ∀ x t u,
      sizeTwoCyclicTargetDifferenceMultiplicity code x t u =
        if u = duplicate x t then 2
        else if u = missing x t then 0 else 1)
    (hdisp : ∀ x t,
      (duplicate x t).1 - (missing x t).1 =
        2 * (t.1 + 1) -
          (((q * (q - 1) / 2 : ℕ) : ZMod q) + 1)) :
    let h2q : 2 ∣ q := dvd_trans (by norm_num : 2 ∣ 4) h4q
    let φ : ZMod q →+* ZMod 2 := ZMod.castHom h2q (ZMod 2)
    ((Finset.univ : Finset
      (ZMod q × sizeTwoAllowedDifference q a)).filter
        fun v => φ (duplicate v.1 v.2).1 = 0).card =
      q * (q / 2 - 1) := by
  dsimp only
  let h2q : 2 ∣ q := dvd_trans (by norm_num : 2 ∣ 4) h4q
  let φ : ZMod q →+* ZMod 2 := ZMod.castHom h2q (ZMod 2)
  have hholes : φ a ≠ φ (-1 - a) := by
    intro h
    have hone : (1 : ZMod 2) = 0 := by
      calc
        1 = φ a - φ (-1 - a) := by
          rw [map_sub, map_neg, map_one]
          generalize φ a = z
          fin_cases z <;> decide
        _ = 0 := sub_eq_zero.mpr h
    exact one_ne_zero hone
  have hcards := sizeTwoAllowedDifference_binaryParity_cards h2q a hholes
  have hparityNe (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
      φ (duplicate x t).1 ≠ φ (missing x t).1 := by
    exact sizeTwoCyclic_singleDuplicateMissing_parity_ne h4q
      (hdisp x t)
  have hne (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
      duplicate x t ≠ missing x t := by
    intro h
    apply hparityNe x t
    rw [h]
  have hopposite (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
      φ (duplicate x t).1 = 0 ↔ φ (missing x t).1 ≠ 0 :=
    zmodTwo_eq_zero_iff_other_ne_zero _ _ (hparityNe x t)
  exact sizeTwoCyclicSharpProfile_duplicateParity_card
    code (fun u => φ u.1 = 0) duplicate missing (q / 2 - 1)
    hcards.1 hcards.2 hne hopposite hprofile

end

end Erdos85

#print axioms
  Erdos85.sizeTwoCyclicSharpProfile_binaryDuplicateParity_card
