import Proofs.Erdos85PositiveExcessDeterminant
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Two-adic parity interface for the defect determinant

This file begins the Smith/valuation obstruction.  Its first lemma isolates
the elementary arithmetic core after denominators have been cleared: an odd
multiple of a square has even two-adic valuation, even when presented as a
rational square with an odd denominator.
-/

namespace Erdos85

/-- If `b n² = c m²` with `c,n` odd, then `v₂(b)` is even.  This is the
cleared-denominator form needed for an integer equal to an odd rational
square multiple. -/
theorem even_padicValNat_two_of_mul_sq_eq_odd_mul_sq
    {b c m n : ℕ} (hb : b ≠ 0) (hc : c ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hcOdd : Odd c) (hnOdd : Odd n)
    (h : b * n ^ 2 = c * m ^ 2) :
    Even (padicValNat 2 b) := by
  have hcNot : ¬2 ∣ c := by
    intro htwo
    exact (Nat.not_even_iff_odd.mpr hcOdd) (even_iff_two_dvd.mpr htwo)
  have hnNot : ¬2 ∣ n := by
    intro htwo
    exact (Nat.not_even_iff_odd.mpr hnOdd) (even_iff_two_dvd.mpr htwo)
  have hcval : padicValNat 2 c = 0 :=
    padicValNat.eq_zero_of_not_dvd hcNot
  have hnval : padicValNat 2 n = 0 :=
    padicValNat.eq_zero_of_not_dvd hnNot
  have hv := congrArg (padicValNat 2) h
  rw [padicValNat.mul hb (pow_ne_zero 2 hn),
    padicValNat.mul hc (pow_ne_zero 2 hm),
    padicValNat.pow, padicValNat.pow, hcval, hnval] at hv
  refine ⟨padicValNat 2 m, ?_⟩
  omega

/-- Rational-square form: an integer which is an odd integer times a
rational square has even two-adic valuation.  Working directly with
`padicValRat` avoids any denominator bookkeeping. -/
theorem even_padicValNat_two_of_eq_odd_mul_rat_sq
    {b c : ℕ} (hb : b ≠ 0) (hc : c ≠ 0) (hcOdd : Odd c)
    (q : ℚ) (hq : q ≠ 0)
    (h : (b : ℚ) = (c : ℚ) * q ^ 2) :
    Even (padicValNat 2 b) := by
  have hcNot : ¬2 ∣ c := by
    intro htwo
    exact (Nat.not_even_iff_odd.mpr hcOdd) (even_iff_two_dvd.mpr htwo)
  have hcval : padicValNat 2 c = 0 :=
    padicValNat.eq_zero_of_not_dvd hcNot
  have hv := congrArg (padicValRat 2) h
  rw [padicValRat.of_nat,
    padicValRat.mul (show (c : ℚ) ≠ 0 by exact_mod_cast hc)
      (pow_ne_zero 2 hq),
    padicValRat.of_nat, padicValRat.pow, hcval] at hv
  rw [even_iff_two_dvd]
  have hdivZ : (2 : ℤ) ∣ (padicValNat 2 b : ℤ) := by
    refine ⟨padicValRat 2 q, ?_⟩
    omega
  exact_mod_cast hdivZ

/-- Integer-valued version, with positivity recovered from the positive odd
factor and the nonzero rational square. -/
theorem even_padicValNat_two_natAbs_of_int_eq_odd_mul_rat_sq
    {z : ℤ} {c : ℕ} (hcPos : 0 < c) (hcOdd : Odd c)
    (q : ℚ) (hq : q ≠ 0)
    (h : (z : ℚ) = (c : ℚ) * q ^ 2) :
    Even (padicValNat 2 z.natAbs) := by
  have hzq : 0 < (z : ℚ) := by
    rw [h]
    exact mul_pos (by positivity) (sq_pos_of_ne_zero hq)
  have hz : 0 < z := by exact_mod_cast hzq
  have habs : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hz.le
  have habsQ := congrArg (fun t : ℤ => (t : ℚ)) habs
  apply even_padicValNat_two_of_eq_odd_mul_rat_sq
    (Int.natAbs_ne_zero.mpr hz.ne') (by omega) hcOdd q hq
  calc
    (z.natAbs : ℚ) = (z : ℚ) := by exact habsQ
    _ = (c : ℚ) * q ^ 2 := h

end Erdos85
