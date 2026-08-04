import Proofs.Erdos85SecondOrderEvenDefect
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Cycle resolvent square factors

Polynomial identities underlying the determinant of `xI-A(C_n)`.
-/

namespace Erdos85

open Polynomial Polynomial.Chebyshev

/-- The standard discriminant identity for the rescaled Chebyshev
polynomials: `C_m^2-4=(X^2-4)S_{m-1}^2`. -/
theorem chebyshev_C_sq_sub_four (m : ℤ) :
    C ℤ m ^ 2 - 4 = (X ^ 2 - 4) * S ℤ (m - 1) ^ 2 := by
  have hs := S_sq_add_S_sq (R := ℤ) (m - 1)
  have hc := C_eq_S_sub_X_mul_S (R := ℤ) m
  rw [show m - 1 + 1 = m by ring] at hs
  rw [hc]
  linear_combination (norm := ring_nf) 4 * hs

/-- Even cycle factors have square class `(X-2)(X+2)`. -/
theorem chebyshev_C_even_sub_two (m : ℤ) :
    C ℤ (2 * m) - 2 =
      (X - 2) * (X + 2) * S ℤ (m - 1) ^ 2 := by
  have hmul := C_mul_C (R := ℤ) m m
  rw [sub_self, C_zero] at hmul
  rw [show m + m = 2 * m by ring] at hmul
  have hdisc := chebyshev_C_sq_sub_four m
  rw [← hmul] at hdisc
  linear_combination (norm := ring_nf) hdisc

/-- Odd cycle factors have square class `X-2`. -/
theorem chebyshev_C_odd_sub_two (m : ℤ) :
    C ℤ (2 * m + 1) - 2 =
      (X - 2) * (S ℤ m + S ℤ (m - 1)) ^ 2 := by
  have hmul := C_mul_C (R := ℤ) m (m + 1)
  have hs := S_sq_add_S_sq (R := ℤ) (m - 1)
  have hrec := S_add_one (R := ℤ) m
  rw [show m + (m + 1) = 2 * m + 1 by ring,
    show m - (m + 1) = -1 by ring, C_neg_one] at hmul
  rw [show m - 1 + 1 = m by ring] at hs
  have hC : C ℤ (2 * m + 1) = C ℤ m * C ℤ (m + 1) - X := by
    linear_combination hmul
  rw [hC, C_eq_S_sub_X_mul_S (R := ℤ) m,
    C_eq_S_sub_X_mul_S (R := ℤ) (m + 1),
    show m + 1 - 1 = m by ring, hrec]
  linear_combination (norm := ring_nf) (X + 2) * hs

/-- Evaluation of the even-cycle factor at the second-order spectral
parameter `d-1`. -/
theorem chebyshev_C_even_eval_secondOrder (d : ℤ) (m : ℤ) :
    (C ℤ (2 * m) - 2).eval (d - 1) =
      (d - 3) * (d + 1) * (S ℤ (m - 1)).eval (d - 1) ^ 2 := by
  rw [chebyshev_C_even_sub_two]
  simp only [eval_mul, eval_sub, eval_add, eval_X, eval_ofNat]
  ring

/-- Evaluation of the odd-cycle factor at the second-order spectral
parameter `d-1`. -/
theorem chebyshev_C_odd_eval_secondOrder (d : ℤ) (m : ℤ) :
    (C ℤ (2 * m + 1) - 2).eval (d - 1) =
      (d - 3) *
        ((S ℤ m + S ℤ (m - 1)).eval (d - 1)) ^ 2 := by
  rw [chebyshev_C_odd_sub_two]
  simp only [eval_mul, eval_sub, eval_add, eval_X, eval_ofNat]
  ring

end Erdos85
