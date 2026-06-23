/-
# Erdős Problem #396 — OQ-04 → OQ-01 → OQ-01 → OQ-03: Catalan numbers are log-convex (the Turán inequality)

The grandparent `Erdos396OQ04OQ01` reads the two-term Catalan recurrence as the
ratio of consecutive Catalan numbers, `r n = (4n+2)/(n+2) = 4 − 6/(n+2)`, and
proves it is **strictly increasing** (`ratio_strictMono`).  The parent
`Erdos396OQ04OQ01OQ01` repackages this as the harmonic **deficit**
`δ n = 4 − r n = 6/(n+2)`.

A strictly increasing ratio of consecutive terms is exactly the statement that the
underlying sequence is **strictly log-convex**.  This file extracts that structural
consequence for the Catalan numbers, in several equivalent forms.

* **`deficit_strictAnti`** : the deficit `δ n = 6/(n+2)` is *strictly decreasing*,
  refining the parent's `δ n → 0` to a monotone descent (equivalently `r n` rises
  monotonically to its supremum `4`).

* **`turan_real`** / **`turan_nat`** : the **Turán inequality**
  `catalan(n+1)² < catalan n · catalan(n+2)`, over `ℝ` and over `ℕ`.  Substituting
  `catalan(n+1) = r n · catalan n` and `catalan(n+2) = r(n+1)·r n·catalan n`, the
  gap is `r n · catalan(n)² · (r(n+1) − r n) > 0`, positive precisely because the
  ratio strictly increases.

* **`hankel_det_pos`** : the `2×2` Hankel minor
  `catalan n · catalan(n+2) − catalan(n+1)² > 0` — Turán phrased as determinant
  positivity of the shifted Catalan moment matrix.

* **`catalan_logConvex`** : the literal log-convexity inequality
  `2·log(catalan(n+1)) < log(catalan n) + log(catalan(n+2))`, obtained by taking
  logarithms of the (positive) Turán inequality.

No Stirling estimate or asymptotic is used; everything follows from the recurrence
ratio and its strict monotonicity established upstream.

Reference: https://erdosproblems.com/396
-/

import Mathlib
import Proofs.Erdos396OQ04OQ01OQ01

open Nat Filter Topology Finset

namespace Erdos396OQ01OQ01OQ03

open Erdos396OQ01 Erdos396OQ01OQ01

/-! ## The deficit descends monotonically -/

/-- **The deficit is strictly decreasing.** `δ n = 6/(n+2)` strictly decreases,
    refining the parent's `δ n → 0` to a monotone descent.  Equivalently the
    ratio `r n = 4 − δ n` rises monotonically to its supremum `4`. -/
theorem deficit_strictAnti : StrictAnti catalanDeficit := by
  intro a b hab
  rw [deficit_eq, deficit_eq]
  have hcast : (a : ℝ) + 2 < (b : ℝ) + 2 := by exact_mod_cast Nat.add_lt_add_right hab 2
  exact div_lt_div_of_pos_left (by norm_num) (by positivity) hcast

/-! ## The Turán inequality (strict log-convexity) -/

/-- The ratio strictly increases by one step: `r n < r (n+1)`. -/
theorem ratio_lt_succ (n : ℕ) : catalanRatio n < catalanRatio (n + 1) :=
  ratio_strictMono (Nat.lt_succ_self n)

/-- **Turán inequality (real form).** `catalan(n+1)² < catalan n · catalan(n+2)`.

    Writing `C(n+1) = r n · C n` and `C(n+2) = r(n+1) · r n · C n`, both sides are
    multiples of `C(n)²`: the difference is `r n · C(n)² · (r(n+1) − r n)`, which is
    positive precisely because the recurrence ratio strictly increases. -/
theorem turan_real (n : ℕ) :
    ((catalan (n + 1) : ℝ)) ^ 2 < (catalan n : ℝ) * (catalan (n + 2) : ℝ) := by
  have e1 := catalan_succ_eq_ratio_mul n
  have e2 := catalan_succ_eq_ratio_mul (n + 1)
  -- express `C(n+2)` purely in terms of `r n`, `r (n+1)`, `C n`
  have e2' : (catalan (n + 2) : ℝ)
      = catalanRatio (n + 1) * (catalanRatio n * (catalan n : ℝ)) := by
    rw [e2, e1]
  rw [e1, e2']
  have hc : (0 : ℝ) < (catalan n : ℝ) := by exact_mod_cast catalan_pos n
  have hc2 : (0 : ℝ) < (catalan n : ℝ) ^ 2 := by positivity
  have hr := ratio_pos n
  have hmono := ratio_lt_succ n
  -- gap = r n · C(n)² · (r(n+1) − r n) > 0
  have key : 0 < catalanRatio n * (catalan n : ℝ) ^ 2
      * (catalanRatio (n + 1) - catalanRatio n) :=
    mul_pos (mul_pos hr hc2) (sub_pos.mpr hmono)
  nlinarith [key]

/-- **Turán inequality (integer form).** `catalan(n+1)² < catalan n · catalan(n+2)`
    as a statement about natural numbers. -/
theorem turan_nat (n : ℕ) : catalan (n + 1) ^ 2 < catalan n * catalan (n + 2) := by
  have h := turan_real n
  exact_mod_cast h

/-- **Hankel-minor positivity.** The `2×2` shifted Catalan moment determinant
    `catalan n · catalan(n+2) − catalan(n+1)²` is strictly positive — the
    determinant phrasing of the Turán inequality. -/
theorem hankel_det_pos (n : ℕ) :
    0 < (catalan n : ℝ) * (catalan (n + 2) : ℝ) - ((catalan (n + 1) : ℝ)) ^ 2 :=
  sub_pos.mpr (turan_real n)

/-! ## Literal log-convexity -/

/-- **Log-convexity of the Catalan numbers.**
    `2·log(catalan(n+1)) < log(catalan n) + log(catalan(n+2))`.

    This is the logarithm of the (strictly positive) Turán inequality: `log` is
    strictly monotone on positives, `log (x²) = 2 log x` and
    `log (x·y) = log x + log y`. -/
theorem catalan_logConvex (n : ℕ) :
    2 * Real.log (catalan (n + 1) : ℝ)
      < Real.log (catalan n : ℝ) + Real.log (catalan (n + 2) : ℝ) := by
  have hc1 : (0 : ℝ) < (catalan (n + 1) : ℝ) := by exact_mod_cast catalan_pos (n + 1)
  have hc0 : (catalan n : ℝ) ≠ 0 := by exact_mod_cast (catalan_pos n).ne'
  have hc2 : (catalan (n + 2) : ℝ) ≠ 0 := by exact_mod_cast (catalan_pos (n + 2)).ne'
  have hlt := Real.log_lt_log (pow_pos hc1 2) (turan_real n)
  rw [Real.log_pow, Real.log_mul hc0 hc2] at hlt
  push_cast at hlt
  linarith [hlt]

/-! ## Sanity checks -/

-- The general theorem specialises at small indices (`catalan` does not kernel-reduce
-- under `decide`, so we instantiate the proven inequality directly).
example : catalan 1 ^ 2 < catalan 0 * catalan 2 := turan_nat 0
example : catalan 2 ^ 2 < catalan 1 * catalan 3 := turan_nat 1
example : catalan 3 ^ 2 < catalan 2 * catalan 4 := turan_nat 2

end Erdos396OQ01OQ01OQ03
