/-
# Shannon AWGN water-filling, oq-03-oq-01 — concavity of the wideband rate in bandwidth

Source: `ShannonChannelCodingAWGNOQ03OQ01EqualNoise.lean`,
`ShannonChannelCodingAWGNOQ03OQ01Supremum.lean` and
`ShannonChannelCodingAWGNOQ03OQ01MonotoneCount.lean` (namespace `ShannonWaterFilling`).
Those files establish, for `n` identical parallel Gaussian channels of noise `c > 0`
sharing a total power budget `P`, that the equal-split rate
`R(n) = (n/2)·log(1 + P/(n·c))` is bounded by the wideband ceiling `P/(2c)`
(`rate_equalNoise_seq_le_wideband`), converges up to it
(`rate_equalNoise_tendsto_wideband`), that `P/(2c)` is the exact supremum
(`rate_equalNoise_iSup_eq_wideband`), and that `R` is **strictly increasing** in the
channel count `n` (`rate_equalNoise_count_strictMonoOn`).

This file supplies the complementary *shape* fact those files left open: the wideband
rate is **strictly concave** in the bandwidth / channel-count variable — the
achievable rate exhibits **diminishing marginal returns**.  Each additional unit of
bandwidth (each extra equal-noise sub-channel) adds strictly *less* rate than the
previous one, even though the total keeps rising toward `P/(2c)`.  Together with the
monotonicity already proved, this pins the qualitative shape of the wideband capacity
curve: strictly increasing, strictly concave, and asymptotic to `P/(2c)` from below.

The engine is the second derivative of the real-variable rate
`g(t) = (t/2)·log(1 + a/t)` on `t > 0` (with `a = P/c > 0`).  From the first
derivative

    g'(t) = ½·(log(1 + a/t) − a/(t+a))      (`hasDerivAt_wideRate`, reused)

a further differentiation gives the strictly negative second derivative

    g''(t) = −½·a² / (t·(t+a)²)  <  0,

so `g` is `StrictConcaveOn (Set.Ioi 0)` via `strictConcaveOn_of_deriv2_neg'`.

Main results (all axiom-free / sorry-free):

* `hasDerivAt_wideRate_deriv` — the derivative of `g'`, i.e. the second derivative
  `g''(t) = −½·a²/(t·(t+a)²)`.
* `wideRate_strictConcaveOn` — `g` is strictly concave on `Set.Ioi 0` (real variable).
* `rate_equalNoise_count_diminishing` — discrete diminishing returns: for `c > 0`,
  `P > 0` and `n ≥ 1`,
  `R(n) + R(n+2) < 2·R(n+1)`,
  i.e. the increments `R(n+1) − R(n)` are strictly decreasing.

Tags: information-theory, shannon, awgn, water-filling, capacity, concave,
diminishing-returns, wideband
-/

import Mathlib
import Proofs.ShannonChannelCodingAWGNOQ03OQ01MonotoneCount

set_option linter.unusedSectionVars false

namespace ShannonWaterFilling

open Set

/-! ## The second derivative of the wideband rate `g(t) = (t/2)·log(1 + a/t)` -/

/-- **Second derivative of the wideband rate function.**  For `a > 0` and `t > 0`,

    `d/dt [ ½·(log(1 + a/t) − a/(t+a)) ] = −½·a² / (t·(t+a)²)`.

The bracketed expression is exactly the first derivative `g'(t)` supplied by
`hasDerivAt_wideRate`.  Differentiating again: `log(1 + a/t)` contributes
`−a/(t·(t+a))` and `a/(t+a)` contributes `−a/(t+a)²`, and their combination collapses
(via `(−(t+a) + t) = −a`) to the single strictly-negative term above. -/
theorem hasDerivAt_wideRate_deriv {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (fun s => (1 / 2) * (Real.log (1 + a / s) - a / (s + a)))
      (-(a ^ 2 / (2 * (t * (t + a) ^ 2)))) t := by
  have htne : t ≠ 0 := ht.ne'
  have hta : (0 : ℝ) < t + a := by linarith
  have htane : t + a ≠ 0 := hta.ne'
  have harg : (0 : ℝ) < 1 + a / t := by
    have : 0 ≤ a / t := div_nonneg ha.le ht.le
    linarith
  have hne : (1 + a / t) ≠ 0 := harg.ne'
  -- derivative of the log term
  have hinvc : HasDerivAt (fun s => a / s) (a * (-(t ^ 2)⁻¹)) t := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv htne).const_mul a
  have hinner : HasDerivAt (fun s => 1 + a / s) (a * (-(t ^ 2)⁻¹)) t := hinvc.const_add 1
  have hlog : HasDerivAt (fun s => Real.log (1 + a / s))
      ((a * (-(t ^ 2)⁻¹)) / (1 + a / t)) t := hinner.log hne
  -- derivative of the fractional term a/(s+a) via the quotient rule
  have hconst : HasDerivAt (fun _ : ℝ => a) 0 t := hasDerivAt_const t a
  have hsum : HasDerivAt (fun s : ℝ => s + a) 1 t := by
    simpa using (hasDerivAt_id t).add_const a
  -- annotate with the pointwise lambda so the function matches (unfolds `Pi.div`)
  have hfrac : HasDerivAt (fun s => a / (s + a))
      ((0 * (t + a) - a * 1) / (t + a) ^ 2) t := hconst.div hsum htane
  -- combine
  have hsub := hlog.sub hfrac
  have hhalf := hsub.const_mul (1 / 2 : ℝ)
  -- rewrite the target derivative value into the raw form produced above; the
  -- compound denominator `1 + a/t` is a sum, which `field_simp` cannot prove nonzero
  -- structurally, so rewrite it to `(t+a)/t` first (only `t`, `t+a` remain).
  have h1 : (1 : ℝ) + a / t = (t + a) / t := by rw [add_div, div_self htne]
  have hval : -(a ^ 2 / (2 * (t * (t + a) ^ 2)))
      = 1 / 2 * (a * -(t ^ 2)⁻¹ / (1 + a / t) - (0 * (t + a) - a * 1) / (t + a) ^ 2) := by
    rw [h1]; field_simp; ring
  rw [hval]
  exact hhalf

/-! ## Strict concavity of the real-variable rate on `t > 0` -/

/-- **The wideband rate `g(t) = (t/2)·log(1 + a/t)` is strictly concave on `t > 0`.**
For `a > 0` the second derivative `−½·a²/(t·(t+a)²)` is strictly negative
(`hasDerivAt_wideRate_deriv`), so `g` is `StrictConcaveOn` on `Set.Ioi 0`.  This is
the real-variable engine behind the discrete diminishing-returns statement below.

The first derivative `deriv g` agrees with `g'` on the open set `Set.Ioi 0`
(via `hasDerivAt_wideRate`), so the second iterated derivative `deriv^[2] g` at any
interior point equals `deriv g'`, which `hasDerivAt_wideRate_deriv` evaluates. -/
theorem wideRate_strictConcaveOn {a : ℝ} (ha : 0 < a) :
    StrictConcaveOn ℝ (Set.Ioi 0) (fun t => t / 2 * Real.log (1 + a / t)) := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioi 0)
  · -- continuity on Ioi 0
    intro x hx
    exact (hasDerivAt_wideRate ha.le (Set.mem_Ioi.mp hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hxpos : 0 < x := Set.mem_Ioi.mp hx
    -- deriv g agrees with g' on a neighbourhood of x
    have hdf : deriv (fun t => t / 2 * Real.log (1 + a / t)) =ᶠ[nhds x]
        (fun s => (1 / 2) * (Real.log (1 + a / s) - a / (s + a))) := by
      filter_upwards [Ioi_mem_nhds hxpos] with y hy
      exact (hasDerivAt_wideRate ha.le (Set.mem_Ioi.mp hy)).deriv
    have h2 : deriv^[2] (fun t => t / 2 * Real.log (1 + a / t)) x
        = deriv (fun s => (1 / 2) * (Real.log (1 + a / s) - a / (s + a))) x := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
      exact hdf.deriv_eq
    rw [h2, (hasDerivAt_wideRate_deriv ha hxpos).deriv]
    have hpos : 0 < a ^ 2 / (2 * (x * (x + a) ^ 2)) := by positivity
    linarith

/-! ## Discrete diminishing returns in the channel count -/

/-- **Diminishing marginal returns of bandwidth.**  For `c > 0`, `P > 0` and `n ≥ 1`,

    `R(n) + R(n+2) < 2·R(n+1)`,   where `R(m) = (m/2)·log(1 + P/(m·c))`,

equivalently `R(n+1) − R(n) > R(n+2) − R(n+1)`: adding one more equal-noise
sub-channel to a bank of `n` raises the rate by *strictly less* than the previous
addition did.  This is the strict midpoint-concavity instance of
`wideRate_strictConcaveOn` at `a = P/c`, evaluated at the integer abscissae
`n < n+1 < n+2` (with `(P/c)/m = P/(m·c)`). -/
theorem rate_equalNoise_count_diminishing {c P : ℝ} (hc : 0 < c) (hP : 0 < P)
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) / 2 * Real.log (1 + P / (n * c))
        + ((n : ℝ) + 2) / 2 * Real.log (1 + P / (((n : ℝ) + 2) * c))
      < 2 * (((n : ℝ) + 1) / 2 * Real.log (1 + P / (((n : ℝ) + 1) * c))) := by
  have ha : 0 < P / c := div_pos hP hc
  have hconc := wideRate_strictConcaveOn ha
  set g : ℝ → ℝ := fun t => t / 2 * Real.log (1 + (P / c) / t) with hg
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hx : (n : ℝ) ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr hnR
  have hy : (n : ℝ) + 2 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hxy : (n : ℝ) ≠ (n : ℝ) + 2 := by linarith
  -- strict concavity at the two abscissae with equal weights 1/2, 1/2
  have hmid := hconc.2 hx hy hxy (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  -- identify the midpoint (1/2)•n + (1/2)•(n+2) = n+1
  have hmidpt : (1 / 2 : ℝ) • (n : ℝ) + (1 / 2 : ℝ) • ((n : ℝ) + 2) = (n : ℝ) + 1 := by
    simp only [smul_eq_mul]; ring
  rw [hmidpt] at hmid
  -- rewrite (P/c)/m = P/(m*c) at the three points
  have em : (P / c) / (n : ℝ) = P / ((n : ℝ) * c) := by rw [div_div, mul_comm c (n : ℝ)]
  have em1 : (P / c) / ((n : ℝ) + 1) = P / (((n : ℝ) + 1) * c) := by
    rw [div_div, mul_comm c ((n : ℝ) + 1)]
  have em2 : (P / c) / ((n : ℝ) + 2) = P / (((n : ℝ) + 2) * c) := by
    rw [div_div, mul_comm c ((n : ℝ) + 2)]
  simp only [hg, smul_eq_mul, em, em1, em2] at hmid
  linarith

end ShannonWaterFilling
