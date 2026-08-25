import Mathlib

/-!
# Arithmetic terminal for the strict private-cut quadratic

The combined-shore collision argument supplies `z² + s ≥ qz`, while the
trade identities give `q/2 ≤ z ≤ s/2`.  For binary orders at least eight,
these inequalities already force `s ≥ 2q - 4`.
-/

namespace Erdos85

/-- Integer form of the strict-cut quadratic terminal. -/
theorem two_mul_sub_four_le_of_strictCut_quadratic_int
    {q m z s : ℤ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hzLower : m ≤ z) (hzUpper : 2 * z ≤ s)
    (hquad : q * z ≤ z ^ 2 + s) :
    2 * q - 4 ≤ s := by
  by_contra hnot
  have hsUpper : s < 2 * q - 4 := lt_of_not_ge hnot
  have hzRight : z ≤ q - 2 := by linarith
  have hm4 : 4 ≤ m := by linarith
  have hmEndpoint : s - m ^ 2 < 0 := by
    nlinarith [sq_nonneg (m - 2)]
  have hqEndpoint : s - 2 * q + 4 < 0 := by linarith
  have hbetween : (z - m) * (z - (q - 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr hzLower) (sub_nonpos.mpr hzRight)
  nlinarith

/-- Natural-number form used by the graph-facing private-cut theorem. -/
theorem two_mul_sub_four_le_of_strictCut_quadratic
    {q m z s : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hzLower : m ≤ z) (hzUpper : 2 * z ≤ s)
    (hquad : q * z ≤ z ^ 2 + s) :
    2 * q - 4 ≤ s := by
  have hqI : (8 : ℤ) ≤ q := by exact_mod_cast hq
  have hqmI : (q : ℤ) = 2 * m := by exact_mod_cast hqm
  have hzLowerI : (m : ℤ) ≤ z := by exact_mod_cast hzLower
  have hzUpperI : 2 * (z : ℤ) ≤ s := by exact_mod_cast hzUpper
  have hquadI : (q : ℤ) * z ≤ (z : ℤ) ^ 2 + s := by exact_mod_cast hquad
  have h := two_mul_sub_four_le_of_strictCut_quadratic_int
    hqI hqmI hzLowerI hzUpperI hquadI
  omega

/-- Equality in the strict-cut lower bound pins the zero-row count. -/
theorem zero_card_eq_sub_two_of_strictCut_quadratic_eq
    {q m z s : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hzLower : m ≤ z) (hzUpper : 2 * z ≤ s)
    (hquad : q * z ≤ z ^ 2 + s)
    (hs : s = 2 * q - 4) :
    z = q - 2 := by
  have hzLe : z ≤ q - 2 := by omega
  by_contra hne
  have hzLt : z < q - 2 := Nat.lt_of_le_of_ne hzLe hne
  have hzStrong : z ≤ q - 3 := by omega
  have hqmI : (q : ℤ) = 2 * m := by exact_mod_cast hqm
  have hzLowerI : (m : ℤ) ≤ z := by exact_mod_cast hzLower
  have hzStrongI' : (z : ℤ) ≤ ((q - 3 : ℕ) : ℤ) := by
    exact_mod_cast hzStrong
  have hqSubI : ((q - 3 : ℕ) : ℤ) = (q : ℤ) - 3 := by omega
  have hzStrongI : (z : ℤ) ≤ (q : ℤ) - 3 := by
    rwa [hqSubI] at hzStrongI'
  have hquadI : (q : ℤ) * z ≤ (z : ℤ) ^ 2 + s := by exact_mod_cast hquad
  have hsI : (s : ℤ) = 2 * q - 4 := by
    rw [hs]
    omega
  have hbetween :
      ((z : ℤ) - m) * ((z : ℤ) - ((q : ℤ) - 3)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr hzLowerI) (sub_nonpos.mpr hzStrongI)
  nlinarith

end Erdos85

#print axioms Erdos85.two_mul_sub_four_le_of_strictCut_quadratic_int
#print axioms Erdos85.two_mul_sub_four_le_of_strictCut_quadratic
#print axioms Erdos85.zero_card_eq_sub_two_of_strictCut_quadratic_eq
