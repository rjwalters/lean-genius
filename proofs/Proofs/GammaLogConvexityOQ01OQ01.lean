import Mathlib

/-
# Gamma Log-Convexity OQ-01-OQ-01: the full weighted geometric-mean inequality

The parent entry `gamma-log-convexity-oq-01` records only the **midpoint**
instance of log-convexity of the Gamma function,
`gamma_midpoint_sq_le : Γ((a+b)/2)² ≤ Γ(a)·Γ(b)` (the case `t = 1/2`, squared).
This leaf upgrades that single point to the **full one-parameter family** — the
exact multiplicative form of log-convexity:

  for `a, b > 0` and `t ∈ [0,1]`,   `Γ(t·a + (1-t)·b) ≤ Γ(a)^t · Γ(b)^(1-t)`,

and then to the **finite (n-point) weighted Jensen** form

  for `xᵢ > 0` and weights `wᵢ ≥ 0` with `∑ wᵢ = 1`,
  `Γ(∑ wᵢ·xᵢ) ≤ ∏ Γ(xᵢ)^(wᵢ)`.

Everything rests on Mathlib's `Real.convexOn_log_Gamma` (log ∘ Γ is convex on
`(0,∞)`): apply two-point convexity (resp. `ConvexOn.map_sum_le`, Jensen) to get
the additive bound on `log Γ`, then exponentiate, turning `t · log Γ(a)` into the
real power `Γ(a)^t` via `Real.log_rpow`. The parent's midpoint inequality is
recovered as the `t = 1/2` case, so this entry genuinely subsumes it.

`0` axioms.
-/

namespace GammaLogConvexityOQ01OQ01

open Real Set

/-- The two-point additive bound from log-convexity of `Γ`: for `a, b > 0` and
`t ∈ [0,1]`, `log Γ(t·a + (1-t)·b) ≤ t·log Γ(a) + (1-t)·log Γ(b)`. This is just
`convexOn_log_Gamma` evaluated at the convex combination, unfolded. -/
lemma logGamma_weighted_le {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.log (Real.Gamma (t * a + (1 - t) * b))
      ≤ t * Real.log (Real.Gamma a) + (1 - t) * Real.log (Real.Gamma b) := by
  have h := convexOn_log_Gamma.2 (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr hb)
    ht0 (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)
  simpa only [Function.comp_apply, smul_eq_mul] using h

/-- **Weighted multiplicative (geometric-mean) inequality for the Gamma function.**
For positive reals `a, b` and a weight `t ∈ [0,1]`,
`Γ(t·a + (1-t)·b) ≤ Γ(a)^t · Γ(b)^(1-t)` (real `rpow` exponents). This is the exact
multiplicative form of log-convexity of `Γ`, generalizing the parent's `t = 1/2`
midpoint inequality to the full family. -/
theorem gamma_weighted_geom_le {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.Gamma (t * a + (1 - t) * b)
      ≤ Real.Gamma a ^ t * Real.Gamma b ^ (1 - t) := by
  have hGa : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hGb : 0 < Real.Gamma b := Real.Gamma_pos_of_pos hb
  -- the argument `t·a + (1-t)·b` is a convex combination of positives, hence positive
  have harg : 0 < t * a + (1 - t) * b := by
    rcases ht0.lt_or_eq with ht | ht
    · exact add_pos_of_pos_of_nonneg (mul_pos ht ha) (mul_nonneg (by linarith) hb.le)
    · rw [← ht]; simpa using hb
  have hRHS : (0 : ℝ) < Real.Gamma a ^ t * Real.Gamma b ^ (1 - t) :=
    mul_pos (Real.rpow_pos_of_pos hGa t) (Real.rpow_pos_of_pos hGb (1 - t))
  -- `log` of the right-hand side equals the additive bound's right-hand side
  have hlogRHS : Real.log (Real.Gamma a ^ t * Real.Gamma b ^ (1 - t))
      = t * Real.log (Real.Gamma a) + (1 - t) * Real.log (Real.Gamma b) := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hGa t).ne' (Real.rpow_pos_of_pos hGb (1 - t)).ne',
      Real.log_rpow hGa, Real.log_rpow hGb]
  -- compare logs, then exponentiate
  have hlog : Real.log (Real.Gamma (t * a + (1 - t) * b))
      ≤ Real.log (Real.Gamma a ^ t * Real.Gamma b ^ (1 - t)) := by
    rw [hlogRHS]; exact logGamma_weighted_le ha hb ht0 ht1
  have hexp := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log (Real.Gamma_pos_of_pos harg), Real.exp_log hRHS] at hexp

/-- **Finite weighted geometric-mean (Jensen) inequality for `Γ`.** For a finite
index set `t`, positive points `xᵢ > 0`, and weights `wᵢ ≥ 0` with `∑ wᵢ = 1`,
`Γ(∑ wᵢ·xᵢ) ≤ ∏ Γ(xᵢ)^(wᵢ)`. The full n-point form of multiplicative log-convexity,
obtained from `ConvexOn.map_sum_le` (Jensen) applied to `log ∘ Γ`. -/
theorem gamma_weighted_geom_le_finset {ι : Type*} (s : Finset ι)
    (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hx : ∀ i ∈ s, 0 < x i) :
    Real.Gamma (∑ i ∈ s, w i * x i) ≤ ∏ i ∈ s, Real.Gamma (x i) ^ w i := by
  -- Jensen on the convex function `log ∘ Γ`
  have hJ := convexOn_log_Gamma.map_sum_le hw hsum (fun i hi => Set.mem_Ioi.mpr (hx i hi))
  simp only [Function.comp_apply, smul_eq_mul] at hJ
  -- some weight is strictly positive (else the weights would sum to `0 ≠ 1`)
  obtain ⟨j, hjs, hjpos⟩ : ∃ i ∈ s, 0 < w i := by
    by_contra hcon
    push_neg at hcon
    have hz : ∑ i ∈ s, w i = 0 :=
      Finset.sum_eq_zero (fun i hi => le_antisymm (hcon i hi) (hw i hi))
    rw [hz] at hsum; exact one_ne_zero hsum.symm
  -- the argument is positive, and so is the product
  have harg : 0 < ∑ i ∈ s, w i * x i :=
    Finset.sum_pos' (fun i hi => mul_nonneg (hw i hi) (hx i hi).le)
      ⟨j, hjs, mul_pos hjpos (hx j hjs)⟩
  have hprodpos : 0 < ∏ i ∈ s, Real.Gamma (x i) ^ w i :=
    Finset.prod_pos (fun i hi => Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos (hx i hi)) _)
  -- `log` of the product is the additive (Jensen) right-hand side
  have hlogprod : Real.log (∏ i ∈ s, Real.Gamma (x i) ^ w i)
      = ∑ i ∈ s, w i * Real.log (Real.Gamma (x i)) := by
    rw [Real.log_prod
      (fun i hi => (Real.rpow_pos_of_pos (Real.Gamma_pos_of_pos (hx i hi)) _).ne')]
    exact Finset.sum_congr rfl
      (fun i hi => Real.log_rpow (Real.Gamma_pos_of_pos (hx i hi)) _)
  have hlog : Real.log (Real.Gamma (∑ i ∈ s, w i * x i))
      ≤ Real.log (∏ i ∈ s, Real.Gamma (x i) ^ w i) := by
    rw [hlogprod]; exact hJ
  have hexp := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log (Real.Gamma_pos_of_pos harg), Real.exp_log hprodpos] at hexp

/-- **Parent midpoint inequality, recovered as the `t = 1/2` case.** For `a, b > 0`,
`Γ((a+b)/2)² ≤ Γ(a)·Γ(b)`: specialize `gamma_weighted_geom_le` at `t = 1/2`
(turning the `1/2`-powers into square roots) and square both nonnegative sides. -/
theorem gamma_midpoint_sq_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.Gamma ((a + b) / 2) ^ 2 ≤ Real.Gamma a * Real.Gamma b := by
  have hmid : 0 < (a + b) / 2 := by linarith
  have h := gamma_weighted_geom_le ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 ≤ 1)
  rw [show (1 : ℝ) / 2 * a + (1 - 1 / 2) * b = (a + b) / 2 by ring,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_mul (Real.Gamma_pos_of_pos ha).le] at h
  -- h : Γ((a+b)/2) ≤ √(Γ a · Γ b); square it
  nlinarith [h, Real.sqrt_nonneg (Real.Gamma a * Real.Gamma b),
    Real.sq_sqrt (mul_nonneg (Real.Gamma_pos_of_pos ha).le (Real.Gamma_pos_of_pos hb).le),
    (Real.Gamma_pos_of_pos hmid).le]

end GammaLogConvexityOQ01OQ01
