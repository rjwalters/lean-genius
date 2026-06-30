/-
  # The distance-to-nearest-integer cosecant bound (Pólya–Vinogradov ingredient)

  The sibling file `BoundedPrimeGapsOQ04OQ01WIP01` proves the **geometric
  exponential sum bound**

      |∑_{n=M+1}^{M+N} e^{2πiθn}| ≤ 1 / |sin(πθ)|        (θ ∉ ℤ).

  In analytic number theory this is almost always used in its sharper,
  geometry-free form in terms of the **distance to the nearest integer**
  `‖θ‖ = |θ − round θ| ∈ [0, 1/2]`:

      |∑_{n=M+1}^{M+N} e^{2πiθn}| ≤ 1 / (2‖θ‖).

  The bridge between the two is the elementary inequality

      |sin(πθ)| ≥ 2‖θ‖                                   (all θ),

  i.e. `1/|sin(πθ)| ≤ 1/(2‖θ‖)`. This file proves exactly that bridge, fully
  machine-checked. It is the cosecant→distance conversion that lets the cotangent
  sum in Pólya–Vinogradov be aggregated as a sum of `1/(2‖a/q‖)` over residues.

  ## Results
  * `two_mul_le_sin_pi_mul`           : `2θ ≤ sin(πθ)` for `θ ∈ [0, 1/2]`
    (the concavity chord bound, via Mathlib's Jordan inequality `le_sin_mul`).
  * `two_mul_abs_le_abs_sin_pi_mul`   : `2|θ| ≤ |sin(πθ)|` for `|θ| ≤ 1/2`.
  * `two_mul_dist_round_le_abs_sin`   : **`2‖θ‖ ≤ |sin(πθ)|`** for every `θ`,
    via `π·ℤ`-periodicity of `|sin|` (`sin_sub_int_mul_pi`).
  * `one_div_abs_sin_le_one_div_two_mul_dist` : the cosecant form
    `1/|sin(πθ)| ≤ 1/(2‖θ‖)` for `θ ∉ ℤ`.

  The engine is Mathlib's Jordan inequality `Real.mul_abs_le_abs_sin`
  (`2/π·|x| ≤ |sin x|` on `|x| ≤ π/2`) together with `abs_sub_round`
  (`‖θ‖ ≤ 1/2`) and the integer-shift identity for `sin`.

  Sibling: BoundedPrimeGapsOQ04OQ01WIP01.lean (the geometric sum bound).
-/

import Mathlib

namespace BoundedPrimeGapsOQ04OQ01Incomplete01

open Real

/-- **Concavity chord bound.** For `θ ∈ [0, 1/2]`, `2θ ≤ sin(πθ)`: the sine curve
on `[0, π/2]` lies above the chord from `(0,0)` to `(1/2, 1)`. -/
theorem two_mul_le_sin_pi_mul {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) :
    2 * θ ≤ Real.sin (π * θ) := by
  have hx0 : (0 : ℝ) ≤ 2 * θ := by linarith
  have hx1 : 2 * θ ≤ 1 := by linarith
  have h := Real.le_sin_mul hx0 hx1
  rwa [show π / 2 * (2 * θ) = π * θ by ring] at h

/-- **The cosecant bound on `[−1/2, 1/2]`.** `2|θ| ≤ |sin(πθ)|` whenever
`|θ| ≤ 1/2`, directly from Mathlib's Jordan inequality with `x = πθ`. -/
theorem two_mul_abs_le_abs_sin_pi_mul {θ : ℝ} (h : |θ| ≤ 1 / 2) :
    2 * |θ| ≤ |Real.sin (π * θ)| := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hx : |π * θ| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos hπ]
    nlinarith [abs_nonneg θ]
  have h2 := Real.mul_abs_le_abs_sin hx
  rw [abs_mul, abs_of_pos hπ] at h2
  rwa [show 2 / π * (π * |θ|) = 2 * |θ| by field_simp] at h2

/-- **The distance-to-nearest-integer cosecant bound.** For *every* real `θ`,

  `2‖θ‖ ≤ |sin(πθ)|`,  where  `‖θ‖ = |θ − round θ|`.

By `π·ℤ`-periodicity `|sin(πθ)| = |sin(π(θ − round θ))|`, and `θ − round θ` lies
in `[−1/2, 1/2]`, where the previous bound applies. -/
theorem two_mul_dist_round_le_abs_sin (θ : ℝ) :
    2 * |θ - round θ| ≤ |Real.sin (π * θ)| := by
  set m : ℤ := round θ with hm
  have hdist : |θ - (m : ℝ)| ≤ 1 / 2 := abs_sub_round θ
  have hkey := two_mul_abs_le_abs_sin_pi_mul (θ := θ - (m : ℝ)) hdist
  have hsin : Real.sin (π * (θ - (m : ℝ))) = (-1) ^ m * Real.sin (π * θ) := by
    rw [mul_sub, show π * (m : ℝ) = (m : ℝ) * π by ring]
    exact Real.sin_sub_int_mul_pi (π * θ) m
  rw [hsin] at hkey
  simpa only [abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul] using hkey

/-- **The cosecant form.** For `θ ∉ ℤ` (equivalently `‖θ‖ ≠ 0`),
`1/|sin(πθ)| ≤ 1/(2‖θ‖)` — the inequality used to bound the geometric exponential
sum of `WIP01` by `1/(2‖θ‖)`. -/
theorem one_div_abs_sin_le_one_div_two_mul_dist (θ : ℝ) (hθ : θ - round θ ≠ 0) :
    1 / |Real.sin (π * θ)| ≤ 1 / (2 * |θ - round θ|) := by
  have hd : 0 < |θ - round θ| := abs_pos.mpr hθ
  have hpos : 0 < 2 * |θ - round θ| := by positivity
  exact one_div_le_one_div_of_le hpos (two_mul_dist_round_le_abs_sin θ)

end BoundedPrimeGapsOQ04OQ01Incomplete01
