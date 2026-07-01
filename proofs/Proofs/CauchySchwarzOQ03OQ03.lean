/-
  Cauchy–Schwarz — Open Question 03 · Sub-Question 03:
  The L^p Interpolation Inequality (log-convexity of the discrete L^p norms)

  The parent proof `cauchy-schwarz-oq-03` develops Hölder's inequality for finite
  sums as the natural generalization of Cauchy–Schwarz.  This file pushes one step
  further to the *interpolation* (log-convexity) inequality:

    ‖f‖_r ≤ ‖f‖_p^θ · ‖f‖_q^{1-θ},   where   1/r = θ/p + (1-θ)/q,  θ ∈ (0,1),

  with the discrete norm ‖f‖_p = (∑_i f_i^p)^{1/p}.  This says exactly that the map
  t ↦ log ‖f‖_{1/t} is convex — the L^p norms are logarithmically convex in the
  reciprocal exponent.  Cauchy–Schwarz / Hölder is the θ = 1/2 midpoint / boundary
  face of this convexity.

  The proof is a single application of Hölder's inequality with the conjugate pair

    a = p/(rθ),   b = q/(r(1-θ)),   1/a + 1/b = r(θ/p + (1-θ)/q) = 1,

  to the split f_i^r = f_i^{rθ} · f_i^{r(1-θ)}, followed by raising to the power 1/r.
  We build the conjugate pair from Mathlib's `Real.HolderConjugate` structure and
  invoke `NNReal.inner_le_Lp_mul_Lq`.

  0 sorries, 0 axioms.
-/

import Mathlib

open Finset NNReal

namespace CauchySchwarzOQ03OQ03

/-- **L^p interpolation inequality (discrete, log-convexity of L^p norms).**

    For `ℝ≥0`-valued `f` on a finite set and exponents with
    `1/r = θ/p + (1-θ)/q` and `θ ∈ (0,1)`,

      `(∑ f_i^r)^{1/r} ≤ (∑ f_i^p)^{θ/p} · (∑ f_i^q)^{(1-θ)/q}`.

    Equivalently `‖f‖_r ≤ ‖f‖_p^θ · ‖f‖_q^{1-θ}`: the reciprocal-exponent map
    `t ↦ log‖f‖_{1/t}` is convex. -/
theorem lp_interpolation_nnreal {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0)
    {p q r θ : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hpqr : 1 / r = θ / p + (1 - θ) / q) :
    (∑ i ∈ s, f i ^ r) ^ (1 / r)
      ≤ (∑ i ∈ s, f i ^ p) ^ (θ / p) * (∑ i ∈ s, f i ^ q) ^ ((1 - θ) / q) := by
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hrθ : (0 : ℝ) < r * θ := by positivity
  have hr1θ : (0 : ℝ) < r * (1 - θ) := by positivity
  -- The conjugate pair a = p/(rθ), b = q/(r(1-θ)).
  set a := p / (r * θ) with ha
  set b := q / (r * (1 - θ)) with hb
  -- The key algebraic identity r·θ/p + r·(1-θ)/q = 1.
  have hsum : r * θ / p + r * (1 - θ) / q = 1 := by
    have h := hpqr
    field_simp at h ⊢
    nlinarith [h]
  have hab : a.HolderConjugate b := by
    refine ⟨?_, ?_, ?_⟩
    · show a⁻¹ + b⁻¹ = (1 : ℝ)⁻¹
      rw [ha, hb, inv_div, inv_div, inv_one]
      exact hsum
    · exact div_pos hp hrθ
    · exact div_pos hq hr1θ
  -- Hölder applied to F_i = f_i^{rθ}, G_i = f_i^{r(1-θ)}.
  have hHolder := NNReal.inner_le_Lp_mul_Lq s
    (fun i => f i ^ (r * θ)) (fun i => f i ^ (r * (1 - θ))) hab
  -- Simplify the three summands pointwise.
  have hexp : r * θ + r * (1 - θ) = r := by ring
  have hprod : ∀ i, (f i ^ (r * θ)) * (f i ^ (r * (1 - θ))) = f i ^ r := by
    intro i
    rw [← NNReal.rpow_add' (by rw [hexp]; exact hr.ne') (f i), hexp]
  have haθ : r * θ * a = p := by rw [ha]; field_simp
  have hbθ : r * (1 - θ) * b = q := by rw [hb]; field_simp
  have hFa : ∀ i, (f i ^ (r * θ)) ^ a = f i ^ p := by
    intro i; rw [← NNReal.rpow_mul, haθ]
  have hGb : ∀ i, (f i ^ (r * (1 - θ))) ^ b = f i ^ q := by
    intro i; rw [← NNReal.rpow_mul, hbθ]
  -- Rewrite Hölder into: ∑ f_i^r ≤ (∑ f_i^p)^{1/a} · (∑ f_i^q)^{1/b}.
  simp only [hprod, hFa, hGb] at hHolder
  -- Raise both sides to the power 1/r ≥ 0 and simplify exponents.
  have hstep : (∑ i ∈ s, f i ^ r) ^ (1 / r)
      ≤ ((∑ i ∈ s, f i ^ p) ^ (1 / a) * (∑ i ∈ s, f i ^ q) ^ (1 / b)) ^ (1 / r) :=
    NNReal.rpow_le_rpow hHolder (by positivity)
  refine hstep.trans_eq ?_
  rw [NNReal.mul_rpow, ← NNReal.rpow_mul, ← NNReal.rpow_mul]
  have hExpP : 1 / a * (1 / r) = θ / p := by rw [ha]; field_simp
  have hExpQ : 1 / b * (1 / r) = (1 - θ) / q := by rw [hb]; field_simp
  rw [hExpP, hExpQ]

/-- **Midpoint (θ = 1/2) case.** With `2/r = 1/p + 1/q`,

      `‖f‖_r ≤ (‖f‖_p · ‖f‖_q)^{1/2}` — the geometric-mean interpolation,
    of which Cauchy–Schwarz is the symmetric instance `p = q`. -/
theorem lp_interpolation_midpoint_nnreal {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpqr : 2 / r = 1 / p + 1 / q) :
    (∑ i ∈ s, f i ^ r) ^ (1 / r)
      ≤ ((∑ i ∈ s, f i ^ p) ^ (1 / p)) ^ (2⁻¹ : ℝ)
        * ((∑ i ∈ s, f i ^ q) ^ (1 / q)) ^ (2⁻¹ : ℝ) := by
  have h : (∑ i ∈ s, f i ^ r) ^ (1 / r)
      ≤ (∑ i ∈ s, f i ^ p) ^ ((1 / 2 : ℝ) / p)
        * (∑ i ∈ s, f i ^ q) ^ ((1 - 1 / 2 : ℝ) / q) := by
    refine lp_interpolation_nnreal s f hp hq hr (by norm_num) (by norm_num) ?_
    rw [one_div r]
    rw [show (1 / 2 : ℝ) / p + (1 - 1 / 2) / q = (2 / r) / 2 by
          rw [hpqr]; ring]
    ring
  refine h.trans_eq ?_
  rw [← NNReal.rpow_mul, ← NNReal.rpow_mul]
  congr 2 <;> ring

end CauchySchwarzOQ03OQ03
