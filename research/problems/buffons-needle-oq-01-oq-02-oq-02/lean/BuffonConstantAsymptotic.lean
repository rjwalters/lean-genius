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

This file proves (REC), monotonicity, and (SQ) completely; the final
real-analysis packaging (rational squeeze + `√` continuity) is isolated as a
single routine step.

Mathlib pin: v4.26.0.  UNREGISTERED companion (not in the gallery build).
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
  ring

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
  rw [slope_def_field, slope_def_field] at key
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
  ring

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
  -- Routine analytic packaging; see the lemmas above for the mathematical content.
  sorry

end BuffonOQ010202
