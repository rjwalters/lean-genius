import Proofs.Erdos85ZModTenSameParityIntertwiner
import Proofs.Erdos85ZModTenSymmetricOddTwoSupport

/-!
# Odd-difference invariance for C10 self-intertwiners

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The usual loopless self-intertwiner theorem controls the doubling-image
(even-difference) checkerboard.  If the cycle superdiagonal also vanishes,
shift the second matrix coordinate by one.  The shifted matrix is loopless,
so the same theorem controls the complementary odd-difference checkerboard.
-/

namespace Erdos85

/-- A C10 self-intertwiner whose cycle superdiagonal vanishes depends only on
coordinate difference also on the odd checkerboard. -/
theorem zmodTen_selfIntertwiner_eq_of_sub_eq_of_odd_of_superdiag_zero
    (H : Matrix (ZMod 10) (ZMod 10) ℤ)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (hsuper : ∀ x, H x (x + 1) = 0)
    {x y x' y' : ZMod 10}
    (hodd : ¬ ZModTenEvenOffset (y - x))
    (hsub : y - x = y' - x') :
    H x y = H x' y' := by
  let H' : Matrix (ZMod 10) (ZMod 10) ℤ := fun i j => H i (j + 1)
  have hdiag' : ∀ z, H' z z = 0 := by
    intro z
    exact hsuper z
  have hinter' : ∀ i j,
      H' (i - 1) j + H' (i + 1) j =
        H' i (j + 1) + H' i (j - 1) := by
    intro i j
    dsimp [H']
    simpa only [show j - 1 + 1 = j by ring,
      show j + 1 + 1 = (j + 1) + 1 by ring,
      show j + 1 - 1 = j by ring] using hinter i (j + 1)
  have hoddHalf : ∀ z : ZMod 10, ¬ ZModTenEvenOffset z →
      z - 1 ∈ Set.range (fun t : ZMod 10 => 2 * t) := by
    decide
  have hhalf : (y - 1) - x ∈ Set.range (fun t : ZMod 10 => 2 * t) := by
    have := hoddHalf (y - x) hodd
    simpa only [show (y - x) - 1 = (y - 1) - x by ring] using this
  have hsub' : (y - 1) - x = (y' - 1) - x' := by
    linear_combination hsub
  have heq := selfIntertwiner_eq_of_sub_eq_of_mem_range_two
    H' hdiag' hinter' hhalf hsub'
  change H x ((y - 1) + 1) = H x' ((y' - 1) + 1) at heq
  simpa using heq

/-- Recurrence-ready odd-support classifier: a symmetric C10
self-intertwiner with zero cycle superdiagonal and exactly two odd-difference
ones per row uses exactly offsets `{±3}`. -/
theorem zmodTen_selfIntertwiner_odd_degreeTwo_offset_three_seven
    (H : Matrix (ZMod 10) (ZMod 10) ℤ)
    (hsymm : ∀ x y, H x y = H y x)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (hsuper : ∀ x, H x (x + 1) = 0)
    (hdegree : ∀ x,
      ((Finset.univ : Finset (ZMod 10)).filter fun y =>
        ¬ ZModTenEvenOffset (y - x) ∧ H x y = 1).card = 2) :
    ∀ x y, ¬ ZModTenEvenOffset (y - x) →
      (H x y = 1 ↔ y - x = 3 ∨ y - x = 7) := by
  classical
  let f : ZMod 10 → Bool := fun z =>
    decide (¬ ZModTenEvenOffset z ∧ H 0 z = 1)
  have hodd_neg_iff : ∀ z : ZMod 10,
      (¬ ZModTenEvenOffset (-z)) ↔ ¬ ZModTenEvenOffset z := by
    decide
  have hneg : ∀ z, f (-z) = f z := by
    intro z
    apply Bool.eq_iff_iff.mpr
    simp only [f, decide_eq_true_eq]
    constructor
    · rintro ⟨hoddNeg, hz⟩
      have hodd : ¬ ZModTenEvenOffset z := (hodd_neg_iff z).1 hoddNeg
      have hodd' : ¬ ZModTenEvenOffset (0 - (-z)) := by
        simpa only [show (0 : ZMod 10) - (-z) = z by ring] using hodd
      refine ⟨hodd, ?_⟩
      calc
        H 0 z = H (-z) 0 :=
          (zmodTen_selfIntertwiner_eq_of_sub_eq_of_odd_of_superdiag_zero
            H hinter hsuper (x := -z) (y := 0) (x' := 0) (y' := z)
              hodd' (by ring)).symm
        _ = H 0 (-z) := hsymm _ _
        _ = 1 := hz
    · rintro ⟨hodd, hz⟩
      have hoddNeg : ¬ ZModTenEvenOffset (-z) := (hodd_neg_iff z).2 hodd
      have hodd' : ¬ ZModTenEvenOffset (0 - (-z)) := by
        simpa only [show (0 : ZMod 10) - (-z) = z by ring] using hodd
      refine ⟨hoddNeg, ?_⟩
      calc
        H 0 (-z) = H (-z) 0 := hsymm _ _
        _ = H 0 z :=
          zmodTen_selfIntertwiner_eq_of_sub_eq_of_odd_of_superdiag_zero
            H hinter hsuper (x := -z) (y := 0) (x' := 0) (y' := z)
              hodd' (by ring)
        _ = 1 := hz
  have hcard :
      ((Finset.univ : Finset (ZMod 10)).filter fun z => f z).card = 2 := by
    simpa [f] using hdegree 0
  have hodd_cases : ∀ z : ZMod 10, ¬ ZModTenEvenOffset z →
      z = 1 ∨ z = 3 ∨ z = 5 ∨ z = 7 ∨ z = 9 := by
    decide
  have hallowed : ∀ z, f z = true → z = 3 ∨ z = 5 ∨ z = 7 := by
    intro z hz
    have hz' : ¬ ZModTenEvenOffset z ∧ H 0 z = 1 := by
      simpa [f] using hz
    have hoddCases := hodd_cases z hz'.1
    rcases hoddCases with h1 | h3 | h5 | h7 | h9
    · subst z
      have hz0 := hsuper 0
      norm_num at hz0
      omega
    · exact Or.inl h3
    · exact Or.inr (Or.inl h5)
    · exact Or.inr (Or.inr h7)
    · subst z
      have hzero : H 0 9 = 0 := by
        have hz0 := hsuper 9
        norm_num at hz0
        calc
          H 0 9 = H 9 0 := hsymm _ _
          _ = 0 := hz0
      omega
  have hf := zmodTen_symmetric_odd_two_support_eq_three_seven
    f hneg hcard hallowed
  intro x y hodd
  have hxy0 : H x y = H 0 (y - x) := by
    apply zmodTen_selfIntertwiner_eq_of_sub_eq_of_odd_of_superdiag_zero
      H hinter hsuper hodd
    ring
  have hf' := hf (y - x)
  simp only [f, decide_eq_true_eq] at hf'
  rw [hxy0]
  simpa [hodd] using hf'

end Erdos85

#print axioms Erdos85.zmodTen_selfIntertwiner_eq_of_sub_eq_of_odd_of_superdiag_zero
#print axioms Erdos85.zmodTen_selfIntertwiner_odd_degreeTwo_offset_three_seven
