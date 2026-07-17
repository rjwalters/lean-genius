/-
# Shannon AWGN water-filling, oq-03-oq-01 — monotonicity in the channel count

Source: `ShannonChannelCodingAWGNOQ03OQ01EqualNoise.lean` and
`ShannonChannelCodingAWGNOQ03OQ01Supremum.lean` (namespace `ShannonWaterFilling`),
which prove that for `n` identical parallel Gaussian channels of noise `c > 0`
sharing a total power budget `P`, the equal-split rate is
`R(n) = (n/2)·log(1 + P/(n·c))`, that every finite `n` is capped by the wideband
ceiling `P/(2c)` (`rate_equalNoise_seq_le_wideband`), that the rates converge up to
that cap (`rate_equalNoise_tendsto_wideband`), and that `P/(2c)` is the exact
supremum (`rate_equalNoise_iSup_eq_wideband`).

This file supplies the missing structural fact those three left open: `R` is
**monotone in the channel count `n`** — splitting a fixed power budget over more
equal-noise sub-channels always increases (never decreases) the achievable rate,
so the sequence climbs *monotonically* to its supremum `P/(2c)` rather than merely
converging to it.

The engine is the real-variable strict monotonicity of `g(t) = (t/2)·log(1 + a/t)`
on `t > 0` (with `a = P/c > 0`), proved from a positive derivative:

    g'(t) = ½·(log(1 + a/t) − a/(t+a))  >  0,

where positivity is the tangent-line inequality `log(1+u) > u/(1+u)` (`u = a/t > 0`),
itself `Real.log_lt_sub_one_of_pos` applied at `x = t/(t+a) ∈ (0,1)`.

Main results (all axiom-free / sorry-free):

* `log_one_add_div_gt` — `a/(t+a) < log(1 + a/t)` for `a, t > 0` (the derivative sign).
* `hasDerivAt_wideRate` — the derivative of `g` at `t > 0`.
* `wideRate_strictMonoOn` — `g` is strictly increasing on `Set.Ioi 0` (real variable).
* `rate_equalNoise_count_strictMonoOn` — `R` is strictly increasing on `n ≥ 1` (for `P > 0`).
* `rate_equalNoise_count_mono` — `R` is `Monotone` over all `n : ℕ` (for `P ≥ 0`).
* `rate_equalNoise_count_lt_wideband` — for `P > 0`, every finite `n` is *strictly*
  below the ceiling: `R(n) < P/(2c)` (the wideband capacity is never attained).

Tags: information-theory, shannon, awgn, water-filling, capacity, monotone, wideband
-/

import Mathlib
import Proofs.ShannonChannelCodingAWGNOQ03OQ01Supremum

set_option linter.unusedSectionVars false

namespace ShannonWaterFilling

open Set

/-! ## The tangent-line inequality driving the derivative sign -/

/-- **`a/(t+a) < log(1 + a/t)` for `a, t > 0`.**  This is the strict tangent-line
bound `log(1+u) > u/(1+u)` with `u = a/t`, obtained by applying the strict inequality
`Real.log_lt_sub_one_of_pos` at `x = t/(t+a) ∈ (0,1)`: there `log x = -log(1 + a/t)`
and `x - 1 = -a/(t+a)`, so `log x < x - 1` rearranges to the claim. -/
theorem log_one_add_div_gt {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    a / (t + a) < Real.log (1 + a / t) := by
  have hta : 0 < t + a := by linarith
  have hx0 : 0 < t / (t + a) := div_pos ht hta
  have hxlt1 : t / (t + a) < 1 := by rw [div_lt_one hta]; linarith
  have hlt := Real.log_lt_sub_one_of_pos hx0 (ne_of_lt hxlt1)
  have e1 : Real.log (t / (t + a)) = - Real.log (1 + a / t) := by
    have h1a : (1 : ℝ) + a / t = (t + a) / t := by field_simp
    rw [h1a, Real.log_div ht.ne' hta.ne', Real.log_div hta.ne' ht.ne']
    ring
  have e2 : t / (t + a) - 1 = -(a / (t + a)) := by field_simp; ring
  rw [e1, e2] at hlt
  linarith

/-! ## The derivative of the real-variable rate `g(t) = (t/2)·log(1 + a/t)` -/

/-- **Derivative of the wideband rate function.**  For `a ≥ 0` and `t > 0`,

    `d/dt [ (t/2)·log(1 + a/t) ] = ½·(log(1 + a/t) − a/(t+a))`.

Built from the product rule (`(t/2)′ = ½`) and the chain rule for `log` composed
with `t ↦ 1 + a/t` (whose derivative is `-a/t²`), then simplified. -/
theorem hasDerivAt_wideRate {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    HasDerivAt (fun s => s / 2 * Real.log (1 + a / s))
      ((1 / 2) * (Real.log (1 + a / t) - a / (t + a))) t := by
  have htne : t ≠ 0 := ht.ne'
  have hta : (0 : ℝ) < t + a := by linarith
  have harg : (0 : ℝ) < 1 + a / t := by
    have : 0 ≤ a / t := div_nonneg ha ht.le
    linarith
  have hne : (1 + a / t) ≠ 0 := harg.ne'
  have hs2 : HasDerivAt (fun s : ℝ => s / 2) (1 / 2 : ℝ) t := by
    simpa using (hasDerivAt_id t).div_const 2
  have hinvc : HasDerivAt (fun s => a / s) (a * (-(t ^ 2)⁻¹)) t := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv htne).const_mul a
  have hinner : HasDerivAt (fun s => 1 + a / s) (a * (-(t ^ 2)⁻¹)) t := hinvc.const_add 1
  have hlog : HasDerivAt (fun s => Real.log (1 + a / s))
      ((a * (-(t ^ 2)⁻¹)) / (1 + a / t)) t := hinner.log hne
  have hmul := hs2.mul hlog
  have heq : (1 / 2) * (Real.log (1 + a / t) - a / (t + a)) =
      (1 / 2) * Real.log (1 + a / t) + t / 2 * ((a * (-(t ^ 2)⁻¹)) / (1 + a / t)) := by
    field_simp
    ring
  rw [heq]
  exact hmul

/-! ## Strict monotonicity of the real-variable rate on `t > 0` -/

/-- **The wideband rate `g(t) = (t/2)·log(1 + a/t)` is strictly increasing on `t > 0`.**
For `a > 0` the derivative `½·(log(1 + a/t) − a/(t+a))` is strictly positive
(`log_one_add_div_gt`), so `g` is `StrictMonoOn` on `Set.Ioi 0`.  This is the
real-variable engine behind the discrete channel-count monotonicity below. -/
theorem wideRate_strictMonoOn {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (fun t => t / 2 * Real.log (1 + a / t)) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx
    exact (hasDerivAt_wideRate ha.le (Set.mem_Ioi.mp hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hxpos : 0 < x := Set.mem_Ioi.mp hx
    rw [(hasDerivAt_wideRate ha.le hxpos).deriv]
    have hkey : a / (x + a) < Real.log (1 + a / x) := log_one_add_div_gt ha hxpos
    linarith

/-! ## Nonnegativity of the discrete rate (raw sequence form) -/

/-- **Nonnegativity of the equal-noise rate, sequence form.**  For `c > 0`, `P ≥ 0`
and any `n : ℕ`, the rate `(n/2)·log(1 + P/(n·c))` is `≥ 0` (including `n = 0`, where
it is `0`). -/
theorem rate_equalNoise_count_nonneg {c P : ℝ} (hc : 0 < c) (hP : 0 ≤ P) (n : ℕ) :
    0 ≤ (n : ℝ) / 2 * Real.log (1 + P / (n * c)) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast h
    have h1 : (1 : ℝ) ≤ 1 + P / (n * c) := by
      have : 0 ≤ P / (n * c) := div_nonneg hP (by positivity)
      linarith
    exact mul_nonneg (by positivity) (Real.log_nonneg h1)

/-! ## Strict monotonicity of the discrete rate in the channel count -/

/-- **Strict channel-count monotonicity of the equal-noise rate.**  For `c > 0` and
`P > 0`, the map `n ↦ (n/2)·log(1 + P/(n·c))` is strictly increasing on `n ≥ 1`:
splitting a fixed positive power budget over more equal-noise sub-channels *strictly*
raises the achievable rate.  This is `wideRate_strictMonoOn` at `a = P/c`, restricted
to the positive integers (with `(P/c)/n = P/(n·c)`). -/
theorem rate_equalNoise_count_strictMonoOn {c P : ℝ} (hc : 0 < c) (hP : 0 < P) :
    StrictMonoOn (fun n : ℕ => (n : ℝ) / 2 * Real.log (1 + P / (n * c))) (Set.Ici 1) := by
  have ha : 0 < P / c := div_pos hP hc
  intro m hm n hn hmn
  have hm1 : (1 : ℕ) ≤ m := Set.mem_Ici.mp hm
  have hn1 : (1 : ℕ) ≤ n := Set.mem_Ici.mp hn
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hmnR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hlt := wideRate_strictMonoOn ha (Set.mem_Ioi.mpr hmR) (Set.mem_Ioi.mpr hnR) hmnR
  have em : (P / c) / (m : ℝ) = P / ((m : ℝ) * c) := by rw [div_div, mul_comm c (m : ℝ)]
  have en : (P / c) / (n : ℝ) = P / ((n : ℝ) * c) := by rw [div_div, mul_comm c (n : ℝ)]
  show (m : ℝ) / 2 * Real.log (1 + P / (m * c)) < (n : ℝ) / 2 * Real.log (1 + P / (n * c))
  rw [← em, ← en]
  exact hlt

/-- **Monotonicity of the equal-noise rate over all channel counts.**  For `c > 0`
and `P ≥ 0`, the sequence `n ↦ (n/2)·log(1 + P/(n·c))` is `Monotone` on all of `ℕ`
(including the degenerate `n = 0` rate `0`).  Combined with
`rate_equalNoise_iSup_eq_wideband`, this shows the rates climb *monotonically* to the
wideband capacity `P/(2c)`, not merely converge to it. -/
theorem rate_equalNoise_count_mono {c P : ℝ} (hc : 0 < c) (hP : 0 ≤ P) :
    Monotone (fun n : ℕ => (n : ℝ) / 2 * Real.log (1 + P / (n * c))) := by
  rcases eq_or_lt_of_le hP with hP0 | hP0
  · intro m n hmn; simp [← hP0]
  · intro m n hmn
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      simp only [Nat.cast_zero, zero_div, zero_mul]
      exact rate_equalNoise_count_nonneg hc hP n
    · have hm1 : (1 : ℕ) ≤ m := hmpos
      have hn1 : (1 : ℕ) ≤ n := le_trans hmpos hmn
      exact (rate_equalNoise_count_strictMonoOn hc hP0).monotoneOn
        (Set.mem_Ici.mpr hm1) (Set.mem_Ici.mpr hn1) hmn

/-! ## The wideband ceiling is never attained at finite bandwidth -/

/-- **Strict wideband gap at every finite channel count.**  For `c > 0` and `P > 0`,
each finite `n` sits *strictly* below the wideband ceiling: `R(n) < P/(2c)`.  For
`n = 0` the rate is `0 < P/(2c)`; for `n ≥ 1` the strict step `R(n) < R(n+1)`
(`rate_equalNoise_count_strictMonoOn`) followed by the per-`n` ceiling
`rate_equalNoise_seq_le_wideband` at `n+1` gives `R(n) < R(n+1) ≤ P/(2c)`.  Thus the
supremum `P/(2c)` is approached but never reached with finitely many sub-channels. -/
theorem rate_equalNoise_count_lt_wideband {c P : ℝ} (hc : 0 < c) (hP : 0 < P) (n : ℕ) :
    (n : ℝ) / 2 * Real.log (1 + P / (n * c)) < P / (2 * c) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero, zero_div, zero_mul]
    exact div_pos hP (mul_pos (by norm_num) hc)
  · have h1 : (1 : ℕ) ≤ n := hpos
    have hstep := rate_equalNoise_count_strictMonoOn hc hP (Set.mem_Ici.mpr h1)
      (Set.mem_Ici.mpr (le_trans h1 (Nat.le_succ n))) (Nat.lt_succ_self n)
    have hle := rate_equalNoise_seq_le_wideband hc hP.le (n + 1)
    exact lt_of_lt_of_le hstep hle

end ShannonWaterFilling
