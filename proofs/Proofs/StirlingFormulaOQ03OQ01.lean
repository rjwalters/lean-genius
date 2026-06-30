/-
An explicit O(1/n) convergence rate for the Wallis product

Source: open question of stirling-formula-oq-03
  ("The Wallis Product as a Standalone Limit: ∏ 4k²/(4k²−1) → π/2")
Status: VERIFIED (0 axioms, 0 sorries, no native_decide)

The parent file `Proofs.StirlingFormulaOQ03` records the *qualitative* Wallis limit
`∏_{k=1}^{n} 4k²/(4k²−1) ⟶ π/2`, obtained by reindexing Mathlib's
`Real.tendsto_prod_pi_div_two`.  A limit statement says nothing about *how fast* the
partial products approach `π/2`.  This file supplies the missing **quantitative**
information: an explicit, fully elementary error bound.

The engine is the pair of two-sided estimates Mathlib already proves for the
partial Wallis product `W k = ∏ i<k, (2i+2)/(2i+1)·(2i+2)/(2i+3)`:

  `Real.Wallis.le_W`  :  `(2k+1)/(2k+2) · (π/2) ≤ W k`
  `Real.Wallis.W_le`  :  `W k ≤ π/2`.

Subtracting the lower bound from `π/2` collapses to a clean closed form,

  `π/2 − W k  ≤  (π/2)·(1/(2k+2))  =  π/(4(k+1))`,

while the upper bound shows the gap is never negative.  Hence

      0  ≤  π/2 − W k  ≤  π / (4(k+1))            (the explicit O(1/n) rate)

and, since `π/4 < 1`, the even cleaner `π/2 − W k ≤ 1/(k+1)`.

We prove:
1. `wallis_gap_nonneg`            — `0 ≤ π/2 − W k` (approach is from below).
2. `wallis_gap_le`               — `π/2 − W k ≤ π/(4(k+1))` (sharp explicit rate).
3. `wallis_gap_le_one_div`        — the cleaner `π/2 − W k ≤ 1/(k+1)` (uses `π < 4`).
4. `abs_W_sub_pi_div_two_le`      — `|W k − π/2| ≤ π/(4(k+1))` (the O(1/n) statement).
5. `wallisProduct_eq_W`           — the classical product equals Mathlib's `W` termwise.
6. `abs_wallisProduct_sub_pi_div_two_le`
                                  — the rate in the parent's textbook form
                                    `|∏_{k=1}^n 4k²/(4k²−1) − π/2| ≤ π/(4(n+1))`.
7. `wallisProduct_tendsto`        — the limit *re-derived from the rate* by squeezing
                                    the error against `π/(4(n+1)) → 0`, confirming the
                                    bound is strong enough to drive convergence.
-/

import Mathlib
import Proofs.StirlingFormulaOQ03

open Filter Topology Real

namespace StirlingFormulaOQ03OQ01

/-! ## Part I: the explicit rate for Mathlib's partial product `W` -/

/-- The Wallis partial product never overshoots `π/2`, so the error `π/2 − W k`
is nonnegative: the sequence approaches its limit strictly from below. -/
theorem wallis_gap_nonneg (k : ℕ) : 0 ≤ π / 2 - Real.Wallis.W k := by
  have h := Real.Wallis.W_le k
  linarith

/-- **Explicit O(1/n) convergence rate.** The error of the `k`-th Wallis partial
product is at most `π/(4(k+1))`:

  `π/2 − W k ≤ π / (4(k+1))`.

This is the quantitative refinement of `Real.tendsto_prod_pi_div_two`. It follows
by subtracting Mathlib's lower bound `Real.Wallis.le_W` from `π/2`, the difference
telescoping to `(π/2)·(1/(2k+2)) = π/(4(k+1))`. -/
theorem wallis_gap_le (k : ℕ) :
    π / 2 - Real.Wallis.W k ≤ π / (4 * ((k : ℝ) + 1)) := by
  have hlb := Real.Wallis.le_W k
  have h2 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
  have h4 : (4 * ((k : ℝ) + 1)) ≠ 0 := by positivity
  -- the lower bound, subtracted from π/2, telescopes to the claimed closed form
  have key : π / 2 - (2 * (k : ℝ) + 1) / (2 * k + 2) * (π / 2)
      = π / (4 * ((k : ℝ) + 1)) := by
    field_simp
    ring
  linarith [hlb, key]

/-- A cleaner (slightly weaker) form of the rate: since `π/4 < 1`,

  `π/2 − W k ≤ 1/(k+1)`. -/
theorem wallis_gap_le_one_div (k : ℕ) :
    π / 2 - Real.Wallis.W k ≤ 1 / ((k : ℝ) + 1) := by
  have hrate := wallis_gap_le k
  have hpi : π ≤ 4 := Real.pi_le_four
  have hpos : (0 : ℝ) < 4 * ((k : ℝ) + 1) := by positivity
  have hstep : π / (4 * ((k : ℝ) + 1)) ≤ 1 / ((k : ℝ) + 1) := by
    rw [div_le_div_iff₀ hpos (by positivity)]
    nlinarith [hpi, (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
  linarith

/-- The O(1/n) rate in absolute-value form: `|W k − π/2| ≤ π/(4(k+1))`. -/
theorem abs_W_sub_pi_div_two_le (k : ℕ) :
    |Real.Wallis.W k - π / 2| ≤ π / (4 * ((k : ℝ) + 1)) := by
  rw [abs_sub_comm, abs_of_nonneg (wallis_gap_nonneg k)]
  exact wallis_gap_le k

/-! ## Part II: transporting the rate to the classical product `∏ 4k²/(4k²−1)` -/

/-- The parent file's classical Wallis product `∏_{k=1}^{n} 4k²/(4k²−1)` is exactly
Mathlib's partial product `W n`: both equal the termwise product
`∏ i<n, (2i+2)/(2i+1)·(2i+2)/(2i+3)`. -/
theorem wallisProduct_eq_W (n : ℕ) :
    StirlingFormulaOQ03.wallisProduct n = Real.Wallis.W n := by
  rw [StirlingFormulaOQ03.wallisProduct_eq]
  rfl

/-- **The explicit rate in textbook form.** The classical Wallis partial product
approaches `π/2` with error `O(1/n)`:

  `|∏_{k=1}^{n} 4k²/(4k²−1) − π/2| ≤ π / (4(n+1))`. -/
theorem abs_wallisProduct_sub_pi_div_two_le (n : ℕ) :
    |StirlingFormulaOQ03.wallisProduct n - π / 2| ≤ π / (4 * ((n : ℝ) + 1)) := by
  rw [wallisProduct_eq_W]
  exact abs_W_sub_pi_div_two_le n

/-! ## Part III: the limit, re-derived from the explicit rate -/

/-- The error bound `π/(4(n+1))` tends to `0`. -/
theorem rate_tendsto_zero :
    Tendsto (fun n : ℕ => π / (4 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ => 4 * ((n : ℝ) + 1)) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).const_mul_atTop
      (by norm_num : (0 : ℝ) < 4)
  exact tendsto_const_nhds.div_atTop hg

/-- **Wallis' limit, re-derived from the rate.** Squeezing the error against the
explicit bound `π/(4(n+1)) → 0` recovers `∏_{k=1}^{n} 4k²/(4k²−1) ⟶ π/2`,
confirming the O(1/n) estimate is strong enough to drive convergence on its own. -/
theorem wallisProduct_tendsto :
    Tendsto StirlingFormulaOQ03.wallisProduct atTop (𝓝 (π / 2)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun n : ℕ => π / (4 * ((n : ℝ) + 1)))
    (fun n => dist_nonneg) (fun n => ?_) rate_tendsto_zero
  rw [Real.dist_eq]
  exact abs_wallisProduct_sub_pi_div_two_le n

end StirlingFormulaOQ03OQ01
