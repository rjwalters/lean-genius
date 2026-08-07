import Mathlib

/-!
# Arithmetic consequences of the minimum-layer design equation

If the restricted minimum-layer quotient has constant row sum `s`, applying
its square equation to the all-ones vector gives

`s² + 3 = u*w + s`,

where `u` is the number of minimum components and `w` their common order.
This file records two uniform consequences: `u` is odd when `w` is odd, and
the discriminant `4uw-11` is a square.
-/

namespace Erdos85

/-- The scalar design equation has discriminant `4uw-11`. -/
theorem minimumLayer_design_discriminant
    (u w s : ℤ) (hdesign : s * s + 3 = u * w + s) :
    (2 * s - 1) ^ 2 = 4 * u * w - 11 := by
  nlinarith

/-- The scalar design equation forces the number of minimum components to
be odd (and in fact forces the product `u*w` to be odd). -/
theorem minimumLayer_card_odd_of_design
    (u w s : ℕ) (hdesign : s * s + 3 = u * w + s) : Odd u := by
  have hprod : Odd (u * w) := by
    by_cases hs0 : s = 0
    · subst s
      norm_num at hdesign
      rw [← hdesign]
      norm_num
    · have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
      have hdesignZ : (s : ℤ) * s + 3 = (u : ℤ) * w + s := by
        exact_mod_cast hdesign
      have hrearrZ : ((u * w : ℕ) : ℤ) =
          ((s * (s - 1) + 3 : ℕ) : ℤ) := by
        push_cast
        rw [Nat.cast_sub hs1]
        ring_nf at hdesignZ ⊢
        linarith
      have hrearr : u * w = s * (s - 1) + 3 := by
        exact_mod_cast hrearrZ
      rw [hrearr]
      exact (Nat.even_mul_pred_self s).add_odd (by norm_num)
  exact (Nat.odd_mul.mp hprod).1

/-- In the nonsquare spectral branch, the trace bound `s ≤ 2u` turns the
design equation into the much sharper order bound `w ≤ 2s`. -/
theorem minimumLayer_order_le_two_mul_rowSum
    (u w s : ℕ) (hs3 : 3 ≤ s)
    (hdesign : s * s + 3 = u * w + s)
    (htrace : s ≤ 2 * u) : w ≤ 2 * s := by
  have hspos : 0 < s := by omega
  have hmul : s * w ≤ (2 * u) * w := Nat.mul_le_mul_right w htrace
  have hdesignZ : (s : ℤ) * s + 3 = (u : ℤ) * w + s := by
    exact_mod_cast hdesign
  have hmulZ : (s : ℤ) * w ≤ (2 * u : ℕ) * w := by
    exact_mod_cast hmul
  have hs3Z : (3 : ℤ) ≤ s := by exact_mod_cast hs3
  have : (w : ℤ) ≤ 2 * s := by nlinarith
  exact_mod_cast this

end Erdos85
