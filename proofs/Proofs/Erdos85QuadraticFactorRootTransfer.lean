import Mathlib

/-!
# Transferring nonquadratic roots to a residual factor
-/

open Polynomial

namespace Erdos85

theorem isRoot_residual_of_quadratic_pow_mul
    {K : Type*} [Field K]
    {P Q : K[X]} (d lambda : K) (k : ℕ)
    (hfactor : P = (X ^ 2 - C d) ^ k * Q)
    (hroot : P.IsRoot lambda) (hne : lambda ^ 2 ≠ d) :
    Q.IsRoot lambda := by
  rw [IsRoot.def, hfactor, eval_mul, eval_pow, eval_sub, eval_pow,
    eval_X, eval_C] at hroot
  rw [IsRoot.def]
  exact (mul_eq_zero.mp hroot).resolve_left
    (pow_ne_zero _ (sub_ne_zero.mpr hne))

end Erdos85
