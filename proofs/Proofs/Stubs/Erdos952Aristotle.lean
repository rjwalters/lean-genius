/-
  Aristotle targets for Erdős Problem #952: The Gaussian Moat Problem
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos952Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the open conjecture (Gaussian moat — whether you can walk to infinity)
  - NOT theorems depending on axiomatized numerical experiments (tsuchimura, etc.)
  - Routine properties of GaussianInt norm and basic arithmetic
  - No definition sorries
  - No axioms

  Included targets (5):
  - gaussianInt_norm_nonneg: GaussianInt.norm z ≥ 0
  - gaussianInt_norm_zero: GaussianInt.norm 0 = 0
  - gaussianInt_norm_one: GaussianInt.norm 1 = 1
  - gaussianInt_norm_mul: GaussianInt.norm (z * w) = norm z * norm w
  - gaussianInt_re_sq_le_norm: z.re ^ 2 ≤ GaussianInt.norm z
-/
import Mathlib

open GaussianInt

namespace Erdos952Aristotle

-- Routine: the norm of a Gaussian integer is nonneg.
-- norm z = z.re^2 + z.im^2 ≥ 0.
theorem gaussianInt_norm_nonneg (z : GaussianInt) : 0 ≤ GaussianInt.norm z := by
  sorry

-- Routine: the norm of 0 is 0.
-- norm 0 = 0^2 + 0^2 = 0.
theorem gaussianInt_norm_zero : GaussianInt.norm (0 : GaussianInt) = 0 := by
  sorry

-- Routine: the norm of 1 is 1.
-- norm 1 = 1^2 + 0^2 = 1.
theorem gaussianInt_norm_one : GaussianInt.norm (1 : GaussianInt) = 1 := by
  sorry

-- Routine: norm is multiplicative.
-- GaussianInt is a normed ring, so norm(z*w) = norm(z)*norm(w).
theorem gaussianInt_norm_mul (z w : GaussianInt) :
    GaussianInt.norm (z * w) = GaussianInt.norm z * GaussianInt.norm w := by
  sorry

-- Routine: the real part squared is at most the norm.
-- z.re^2 ≤ z.re^2 + z.im^2 = norm z since z.im^2 ≥ 0.
theorem gaussianInt_re_sq_le_norm (z : GaussianInt) : z.re ^ 2 ≤ GaussianInt.norm z := by
  sorry

end Erdos952Aristotle
