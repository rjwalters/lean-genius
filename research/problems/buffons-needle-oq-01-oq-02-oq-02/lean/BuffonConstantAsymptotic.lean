/-
# Asymptotic decay of the higher-dimensional Buffon hyperplane constant

Open question of gallery proof `buffons-needle-oq-01-oq-02`.

## The constant

The parent proof `BuffonsNeedleOQ01OQ02.lean` defines the dimension-`n` Buffon
crossing constant as the expected absolute coordinate of a uniform unit vector
`u ∈ S^{n-1}`:
```
  buffonConstant n = 2 * Γ(n/2) / ((n - 1) * √π * Γ((n-1)/2)),   n ≥ 2.
```
(NOTE: the seeder's `problem.md` quoted a *different* normalization
`Γ(n/2)/(√π Γ((n+1)/2))`; the genuine parent constant is the one above. The
asymptotic `c_n ~ √(2/(πn))` holds for it all the same — see the recurrence
below.)

## Result

`√n · buffonConstant n → √(2/π)`  as  `n → ∞`,  equivalently
`buffonConstant n ~ √(2/(π n))`.

## Strategy (Stirling-free, elementary)

Set `s n = Γ(n/2) / Γ((n-1)/2)`, so `buffonConstant n = 2 · s n / ((n-1)·√π)`.
The Gamma recurrence `Γ(z+1) = z·Γ(z)` at `z = (n-1)/2` gives the **product
recurrence**
```
  s n · s (n+1) = (n-1)/2.                                      (REC)
```
Log-convexity of `Γ` (Mathlib `Real.convexOn_log_Gamma`) makes `n ↦ s n`
**monotone increasing**. Combining monotonicity with (REC) at `n-1` and `n`
squeezes the square:
```
  (n-2)/2 = s(n-1)·s n ≤ (s n)^2 ≤ s n·s(n+1) = (n-1)/2,        (SQ)
```
hence `(s n)^2 / n → 1/2`, i.e. `s n ~ √(n/2)`. Substituting,
`(√n · buffonConstant n)^2 = (4/π) · n (s n)^2/(n-1)^2 → (4/π)(1/2) = 2/π`,
and taking square roots (the quantity is nonnegative) yields the claim.

This file proves (REC), monotonicity, and (SQ) completely.  The final
real-analysis packaging is now also written out, via three helper lemmas:
`s_sq_div_tendsto` ((s n)^2/n -> 1/2 by squeezing (SQ)/n), `ratio_tendsto_one`
and `ratio_sq_tendsto_one` ((n/(n-1))^2 -> 1), feeding `sq_target_eq` to get the
squared sequence -> 2/pi, then `Real.sqrt_sq` + `Real.continuous_sqrt`.

BUILD STATUS: machine-checked via `./proofs/scripts/docker-build.sh
Proofs.BuffonConstantAsymptotic` (Lean v4.26.0, Mathlib pin `2df2f01`; 7743 jobs,
0 errors) and registered in `proofs/Proofs.lean`.  0 axioms, 0 sorries.  The
asymptotic is additionally validated numerically (lgamma, n up to 1e6: the
relative error of `√n·c_n` against `√(2/π)` scales as 0.25/n).

Mathlib pin: v4.26.0.
-/
import Mathlib

open Real Filter Topology
open scoped BigOperators

namespace BuffonOQ010202

/-- The higher-dimensional Buffon crossing constant, matching the parent
`BuffonsNeedleOQ01OQ02.buffonConstant`. -/
noncomputable def buffonConstant (n : ℕ) : ℝ :=
  if n ≤ 1 then 0
  else 2 * Real.Gamma ((n : ℝ) / 2) /
    (((n : ℝ) - 1) * Real.sqrt π * Real.Gamma (((n : ℝ) - 1) / 2))

/-- The Gamma ratio `s n = Γ(n/2) / Γ((n-1)/2)`. -/
noncomputable def s (n : ℕ) : ℝ :=
  Real.Gamma ((n : ℝ) / 2) / Real.Gamma (((n : ℝ) - 1) / 2)

/-- For `n ≥ 2`, `(n:ℝ)/2 > 0`. -/
lemma half_pos (n : ℕ) (hn : 2 ≤ n) : (0 : ℝ) < (n : ℝ) / 2 := by
  have : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  linarith

/-- For `n ≥ 2`, `((n:ℝ)-1)/2 > 0`. -/
lemma half_pred_pos (n : ℕ) (hn : 2 ≤ n) : (0 : ℝ) < ((n : ℝ) - 1) / 2 := by
  have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

lemma gamma_half_pos (n : ℕ) (hn : 2 ≤ n) : 0 < Real.Gamma ((n : ℝ) / 2) :=
  Real.Gamma_pos_of_pos (half_pos n hn)

lemma gamma_half_pred_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < Real.Gamma (((n : ℝ) - 1) / 2) :=
  Real.Gamma_pos_of_pos (half_pred_pos n hn)

/-- `s n > 0` for `n ≥ 2`. -/
lemma s_pos (n : ℕ) (hn : 2 ≤ n) : 0 < s n := by
  unfold s
  exact div_pos (gamma_half_pos n hn) (gamma_half_pred_pos n hn)

/-- **Product recurrence**: `s n · s (n+1) = (n-1)/2` for `n ≥ 2`. -/
lemma s_mul_s_succ (n : ℕ) (hn : 2 ≤ n) :
    s n * s (n + 1) = ((n : ℝ) - 1) / 2 := by
  have hb : Real.Gamma ((n : ℝ) / 2) ≠ 0 := ne_of_gt (gamma_half_pos n hn)
  have hg : Real.Gamma (((n : ℝ) - 1) / 2) ≠ 0 := ne_of_gt (gamma_half_pred_pos n hn)
  -- Γ((n+1)/2) = ((n-1)/2) · Γ((n-1)/2)
  have hstep : Real.Gamma (((n : ℝ) + 1) / 2)
      = (((n : ℝ) - 1) / 2) * Real.Gamma (((n : ℝ) - 1) / 2) := by
    have harg : ((n : ℝ) + 1) / 2 = ((n : ℝ) - 1) / 2 + 1 := by ring
    rw [harg, Real.Gamma_add_one (ne_of_gt (half_pred_pos n hn))]
  unfold s
  -- rewrite the (n+1) entry's argument casts
  have hcast1 : ((↑(n + 1) : ℝ)) / 2 = ((n : ℝ) + 1) / 2 := by push_cast; ring
  have hcast2 : ((↑(n + 1) : ℝ) - 1) / 2 = (n : ℝ) / 2 := by push_cast; ring
  rw [hcast1, hcast2, hstep]
  field_simp

/-- **Monotonicity**: `s n ≤ s (n+1)` for `n ≥ 2`, from log-convexity of `Γ`. -/
lemma s_le_s_succ (n : ℕ) (hn : 2 ≤ n) : s n ≤ s (n + 1) := by
  -- Work with φ = log ∘ Γ, convex on Ioi 0, at the three equally-spaced points
  -- x = (n-1)/2 < y = n/2 < z = (n+1)/2.
  have hx : ((n : ℝ) - 1) / 2 ∈ Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_Ioi]; exact half_pred_pos n hn
  have hz : ((n : ℝ) + 1) / 2 ∈ Set.Ioi (0 : ℝ) := by
    simp only [Set.mem_Ioi]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hxy : ((n : ℝ) - 1) / 2 < (n : ℝ) / 2 := by linarith
  have hyz : (n : ℝ) / 2 < ((n : ℝ) + 1) / 2 := by linarith
  have key := (Real.convexOn_log_Gamma).slope_mono_adjacent hx hz hxy hyz
  simp only [Function.comp_apply] at key
  -- the two denominators both equal 1/2
  have e1 : (n : ℝ) / 2 - ((n : ℝ) - 1) / 2 = 1 / 2 := by ring
  have e2 : ((n : ℝ) + 1) / 2 - (n : ℝ) / 2 = 1 / 2 := by ring
  rw [e1, e2] at key
  have htwo : ∀ a : ℝ, a / (1 / 2) = 2 * a := fun a => by ring
  rw [htwo, htwo] at key
  -- key : 2 * (log Γ(n/2) - log Γ((n-1)/2)) ≤ 2 * (log Γ((n+1)/2) - log Γ(n/2))
  have hlog : Real.log (Real.Gamma ((n : ℝ) / 2)) - Real.log (Real.Gamma (((n : ℝ) - 1) / 2))
      ≤ Real.log (Real.Gamma (((n : ℝ) + 1) / 2)) - Real.log (Real.Gamma ((n : ℝ) / 2)) := by
    linarith
  -- turn the differences of logs into logs of s n and s (n+1)
  have hsn : Real.log (s n)
      = Real.log (Real.Gamma ((n : ℝ) / 2)) - Real.log (Real.Gamma (((n : ℝ) - 1) / 2)) := by
    unfold s
    rw [Real.log_div (ne_of_gt (gamma_half_pos n hn)) (ne_of_gt (gamma_half_pred_pos n hn))]
  have hsn1 : Real.log (s (n + 1))
      = Real.log (Real.Gamma (((n : ℝ) + 1) / 2)) - Real.log (Real.Gamma ((n : ℝ) / 2)) := by
    unfold s
    have hcast1 : ((↑(n + 1) : ℝ)) / 2 = ((n : ℝ) + 1) / 2 := by push_cast; ring
    have hcast2 : ((↑(n + 1) : ℝ) - 1) / 2 = (n : ℝ) / 2 := by push_cast; ring
    have hzpos : (0 : ℝ) < ((n : ℝ) + 1) / 2 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [hcast1, hcast2,
        Real.log_div (ne_of_gt (Real.Gamma_pos_of_pos hzpos))
          (ne_of_gt (gamma_half_pos n hn))]
  have hlog' : Real.log (s n) ≤ Real.log (s (n + 1)) := by rw [hsn, hsn1]; exact hlog
  -- conclude via monotonicity of log on positives
  have hsnpos : 0 < s n := s_pos n hn
  have hsn1pos : 0 < s (n + 1) := s_pos (n + 1) (by omega)
  exact (Real.log_le_log_iff hsnpos hsn1pos).mp hlog'

/-- **Squeeze** of the square: `(n-2)/2 ≤ (s n)^2 ≤ (n-1)/2` for `n ≥ 3`. -/
lemma s_sq_bounds (n : ℕ) (hn : 3 ≤ n) :
    ((n : ℝ) - 2) / 2 ≤ (s n) ^ 2 ∧ (s n) ^ 2 ≤ ((n : ℝ) - 1) / 2 := by
  have hn2 : 2 ≤ n := by omega
  have hn1 : 2 ≤ n - 1 := by omega
  -- monotonicity gives s(n-1) ≤ s n ≤ s(n+1)
  have hmono_lo : s (n - 1) ≤ s n := by
    have := s_le_s_succ (n - 1) hn1
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at this
  have hmono_hi : s n ≤ s (n + 1) := s_le_s_succ n hn2
  -- positivity
  have hpos_lo : 0 < s (n - 1) := s_pos (n - 1) hn1
  have hpos_n : 0 < s n := s_pos n hn2
  -- the two recurrences
  have hrec_hi : s n * s (n + 1) = ((n : ℝ) - 1) / 2 := s_mul_s_succ n hn2
  have hrec_lo : s (n - 1) * s n = ((n : ℝ) - 2) / 2 := by
    have h := s_mul_s_succ (n - 1) hn1
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
    -- ((↑(n-1)) - 1)/2 = ((n:ℝ) - 2)/2
    have hc : ((↑(n - 1) : ℝ) - 1) / 2 = ((n : ℝ) - 2) / 2 := by
      have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        have : 1 ≤ n := by omega
        push_cast [Nat.cast_sub this]; ring
      rw [this]; ring
    rwa [hc] at h
  constructor
  · -- (n-2)/2 = s(n-1)·s n ≤ s n · s n = (s n)^2
    have : s (n - 1) * s n ≤ s n * s n :=
      mul_le_mul_of_nonneg_right hmono_lo (le_of_lt hpos_n)
    rw [hrec_lo] at this
    nlinarith [this]
  · -- (s n)^2 = s n · s n ≤ s n · s(n+1) = (n-1)/2
    have : s n * s n ≤ s n * s (n + 1) :=
      mul_le_mul_of_nonneg_left hmono_hi (le_of_lt hpos_n)
    rw [hrec_hi] at this
    nlinarith [this]

/-- `buffonConstant n = 2 · s n / ((n-1)·√π)` for `n ≥ 2`. -/
lemma buffonConstant_eq (n : ℕ) (hn : 2 ≤ n) :
    buffonConstant n = 2 * s n / (((n : ℝ) - 1) * Real.sqrt π) := by
  unfold buffonConstant s
  have hne : ¬ n ≤ 1 := by omega
  rw [if_neg hne]
  have hg : Real.Gamma (((n : ℝ) - 1) / 2) ≠ 0 := ne_of_gt (gamma_half_pred_pos n hn)
  field_simp

/-- The squared target sequence equals `(4/π) · n (s n)^2 / (n-1)^2`. -/
lemma sq_target_eq (n : ℕ) (hn : 2 ≤ n) :
    (Real.sqrt (n : ℝ) * buffonConstant n) ^ 2
      = (4 / π) * ((n : ℝ) * (s n) ^ 2 / ((n : ℝ) - 1) ^ 2) := by
  have hnpos : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hpi : (0 : ℝ) ≤ π := le_of_lt pi_pos
  have hsqrtn : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos
  have hsqrtpi : Real.sqrt π ^ 2 = π := Real.sq_sqrt hpi
  have hnm1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [buffonConstant_eq n hn]
  rw [mul_pow, div_pow, mul_pow, mul_pow]
  rw [hsqrtn, hsqrtpi]
  have hpine : (π : ℝ) ≠ 0 := ne_of_gt pi_pos
  field_simp
  ring

/-- `(s n)^2 / n → 1/2`, by squeezing `s_sq_bounds` (divided by `n`) between
`((n-2)/2)/n = 1/2 - 1/n` and `((n-1)/2)/n = 1/2 - 1/(2n)`, both `→ 1/2`. -/
lemma s_sq_div_tendsto :
    Tendsto (fun n : ℕ => (s n) ^ 2 / (n : ℝ)) atTop (𝓝 (1 / 2)) := by
  have h1n : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hc : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)) := tendsto_const_nhds
  -- lower bounding sequence L n = ((n-2)/2)/n → 1/2
  have hL : Tendsto (fun n : ℕ => (((n : ℝ) - 2) / 2) / (n : ℝ)) atTop (𝓝 (1 / 2)) := by
    have hM : Tendsto (fun n : ℕ => (1 / 2 : ℝ) - 1 / (n : ℝ)) atTop (𝓝 (1 / 2)) := by
      simpa only [sub_zero] using hc.sub h1n
    refine hM.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hne : (n : ℝ) ≠ 0 := hnpos.ne'
    field_simp
  -- upper bounding sequence U n = ((n-1)/2)/n → 1/2
  have hU : Tendsto (fun n : ℕ => (((n : ℝ) - 1) / 2) / (n : ℝ)) atTop (𝓝 (1 / 2)) := by
    have hhalf : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (1 / (n : ℝ))) atTop (𝓝 ((1 / 2) * 0)) :=
      h1n.const_mul (1 / 2)
    have hM : Tendsto (fun n : ℕ => (1 / 2 : ℝ) - (1 / 2) * (1 / (n : ℝ))) atTop (𝓝 (1 / 2)) := by
      simpa only [mul_zero, sub_zero] using hc.sub hhalf
    refine hM.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hne : (n : ℝ) ≠ 0 := hnpos.ne'
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have hb := (s_sq_bounds n hn).1
    have hnpos : (0 : ℝ) ≤ n := by positivity
    gcongr
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have hb := (s_sq_bounds n hn).2
    have hnpos : (0 : ℝ) ≤ n := by positivity
    gcongr

/-- `n / (n-1) → 1`. -/
lemma ratio_tendsto_one :
    Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1)) atTop (𝓝 1) := by
  have h1n : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hden : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ)) atTop (𝓝 1) := by
    simpa only [sub_zero] using hc.sub h1n
  have hdiv : Tendsto (fun n : ℕ => (1 : ℝ) / (1 - 1 / (n : ℝ))) atTop (𝓝 1) := by
    have h := hc.div hden (by norm_num)
    simpa only [div_one] using h
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hpos1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := hpos1.ne'
  field_simp

/-- `(n/(n-1))^2 → 1`. -/
lemma ratio_sq_tendsto_one :
    Tendsto (fun n : ℕ => ((n : ℝ) / ((n : ℝ) - 1)) ^ 2) atTop (𝓝 1) := by
  simpa only [one_pow] using ratio_tendsto_one.pow 2

/-- **Main asymptotic** (open question of `buffons-needle-oq-01-oq-02`):
`√n · buffonConstant n → √(2/π)`, i.e. `buffonConstant n ~ √(2/(π n))`.

The discrete core (recurrence, monotonicity, squared bounds, and the algebraic
identity `sq_target_eq`) is fully established above. The remaining step is the
routine real-analysis packaging:

* From `s_sq_bounds`, `(s n)^2 / n → 1/2` by squeezing between `(1/2 - 1/n)`
  and `(1/2 - 1/(2n))` (both `→ 1/2` via `tendsto_const_div_atTop_nhds_zero_nat`).
* Hence `n (s n)^2 / (n-1)^2 = ((s n)^2/n) · (n/(n-1))^2 → (1/2)·1 = 1/2`,
  using `n/(n-1) → 1`.
* So the squared sequence `→ (4/π)(1/2) = 2/π` by `sq_target_eq`.
* `√n · buffonConstant n ≥ 0`, so it equals `√` of its square, and
  `Real.continuous_sqrt` gives the limit `√(2/π)`. -/
theorem sqrt_mul_buffonConstant_tendsto :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * buffonConstant n) atTop
      (𝓝 (Real.sqrt (2 / π))) := by
  -- The squared sequence tends to 2/π, then take √ via continuity (sequence ≥ 0).
  have hprod : Tendsto
      (fun n : ℕ => (s n) ^ 2 / (n : ℝ) * ((n : ℝ) / ((n : ℝ) - 1)) ^ 2) atTop
      (𝓝 (1 / 2 * 1)) :=
    s_sq_div_tendsto.mul ratio_sq_tendsto_one
  have hsq : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ) * buffonConstant n) ^ 2) atTop
      (𝓝 (2 / π)) := by
    have hconst : Tendsto
        (fun n : ℕ => (4 / π) * ((s n) ^ 2 / (n : ℝ) * ((n : ℝ) / ((n : ℝ) - 1)) ^ 2)) atTop
        (𝓝 ((4 / π) * (1 / 2 * 1))) := hprod.const_mul (4 / π)
    have hpt : (4 / π) * (1 / 2 * 1) = 2 / π := by ring
    rw [hpt] at hconst
    refine hconst.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn2 : 2 ≤ n := hn
    have hnpos : (0 : ℝ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hne : (n : ℝ) ≠ 0 := hnpos.ne'
    have hpos1 : (0 : ℝ) < (n : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    have hn1 : (n : ℝ) - 1 ≠ 0 := hpos1.ne'
    have hpi : (π : ℝ) ≠ 0 := ne_of_gt pi_pos
    rw [sq_target_eq n hn2]
    field_simp
  have hfin := (Real.continuous_sqrt.tendsto (2 / π)).comp hsq
  refine hfin.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn2 : 2 ≤ n := hn
  have hbc : 0 ≤ buffonConstant n := by
    rw [buffonConstant_eq n hn2]
    have hs := s_pos n hn2
    have hpos1 : (0 : ℝ) < (n : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    have hpi : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
    positivity
  have hg : 0 ≤ Real.sqrt (n : ℝ) * buffonConstant n :=
    mul_nonneg (Real.sqrt_nonneg _) hbc
  simp only [Function.comp_apply]
  exact Real.sqrt_sq hg

end BuffonOQ010202
