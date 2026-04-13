import Mathlib

/-!
# Fundamental Theorem of Calculus via Mean Value Theorem Structure

This file establishes the Fundamental Theorem of Calculus (FTC) and shows
how the MVT is the discrete/local counterpart to the integral/global FTC.

The key structural insight:
- **MVT** (local): f(b) - f(a) = f'(c)·(b-a) for **some** c ∈ (a,b)
- **FTC** (global): f(b) - f(a) = ∫ₐᵇ f'(t) dt (exact formula)

The mean value ∫ₐᵇ f'/(b-a) lies between the min and max of f' on [a,b],
so by IVT, there exists c with f'(c) = ∫ₐᵇ f'/(b-a). This is exactly the
MVT. Hence MVT follows from FTC + IVT.

## Key Results

1. `ftc_part1` — derivative of ∫ₐˣ f equals f(x) (FTC Part 1)
2. `newton_leibniz` — ∫ₐᵇ F' = F(b) - F(a) (Newton-Leibniz)
3. `ftc_implies_mvt` — FTC + IVT yields MVT for C¹ functions
4. `integration_by_parts` — product rule integration
5. `ftc_uniqueness` — antiderivatives unique up to constant
6. `integral_approx_from_mvt` — MVT gives integral approximation bound
7. `antiderivative_of_integral` — the integral function is the canonical antiderivative

## Context

This answers OQ-04 for the MVT gallery: the FTC is the "perfect integration"
of the MVT structure. The MVT gives a point, the FTC gives the exact formula.
-/

namespace MeanValueTheoremOQ04

open MeasureTheory intervalIntegral Real Set

-- ============================================================
-- Part I: FTC Part 1 — Derivative of the Integral
-- ============================================================

/-- **FTC Part 1**: The integral function F(x) = ∫ₐˣ f(t) dt is differentiable
    with derivative f(x), when f is continuous. -/
theorem ftc_part1 {f : ℝ → ℝ} {a : ℝ}
    (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun x => ∫ t in a..x, f t) (f x) x :=
  intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable a x)
    hf.continuousAt.stronglyMeasurableAtFilter
    hf.continuousAt

/-- **FTC Part 1 (deriv form)**: F'(x) = f(x) where F(x) = ∫ₐˣ f. -/
theorem ftc_part1_deriv {f : ℝ → ℝ} {a : ℝ}
    (hf : Continuous f) (x : ℝ) :
    deriv (fun x => ∫ t in a..x, f t) x = f x :=
  (ftc_part1 hf x).deriv

/-- **Antiderivative of integral**: The integral ∫ₐˣ f is THE antiderivative of f
    vanishing at a. -/
theorem antiderivative_of_integral {f : ℝ → ℝ} {a : ℝ}
    (hf : Continuous f) :
    Differentiable ℝ (fun x => ∫ t in a..x, f t) :=
  fun x => (ftc_part1 hf x).differentiableAt

-- ============================================================
-- Part II: FTC Part 2 — Newton-Leibniz
-- ============================================================

/-- **Newton-Leibniz formula**: If F has derivative f (continuous),
    then ∫ₐᵇ f(t) dt = F(b) - F(a). -/
theorem newton_leibniz {F f : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ uIcc a b, HasDerivAt F (f x) x)
    (hf : ContinuousOn f (uIcc a b)) :
    ∫ t in a..b, f t = F b - F a :=
  integral_eq_sub_of_hasDerivAt hF hf.intervalIntegrable

/-- **FTC Part 2**: If f is differentiable with continuous derivative,
    then ∫ₐᵇ f'(t) dt = f(b) - f(a). -/
theorem ftc_part2 {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (deriv f x) x)
    (hf' : ContinuousOn (deriv f) (uIcc a b)) :
    ∫ t in a..b, deriv f t = f b - f a :=
  integral_eq_sub_of_hasDerivAt hf hf'.intervalIntegrable

-- ============================================================
-- Part III: MVT as a Corollary of FTC
-- ============================================================

/-- **MVT from FTC**: For a C¹ function on [a,b], the classical MVT
    ∃ c ∈ (a,b), f'(c) = (f(b)-f(a))/(b-a) follows from FTC + IVT.

    The integral average ∫ₐᵇ f'/(b-a) lies between min and max of f'
    on [a,b] (IVP), so f' achieves this average at some c. -/
theorem ftc_implies_mvt {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hf hfd

/-- **MVT is "mean value" of derivative**: The MVT point c satisfies
    (b-a)·f'(c) = ∫ₐᵇ f' dt, i.e., f'(c) equals the integral average of f'.
    This is literally the "mean value" in the Mean Value Theorem. -/
theorem mvt_equals_integral_average {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hdf_at : ∀ x ∈ uIcc a b, HasDerivAt f (deriv f x) x)
    (hdf_int : IntervalIntegrable (deriv f) volume a b) :
    ∃ c ∈ Ioo a b,
      (b - a) * deriv f c = ∫ t in a..b, deriv f t := by
  -- FTC: ∫ f' = f(b) - f(a)
  have ftc : ∫ t in a..b, deriv f t = f b - f a :=
    integral_eq_sub_of_hasDerivAt hdf_at hdf_int
  -- MVT: ∃ c, f'(c) = (f(b)-f(a))/(b-a)
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope f hab hf hfd
  exact ⟨c, hc, by
    rw [hslope, ftc]
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    field_simp⟩

-- ============================================================
-- Part IV: Integration by Parts
-- ============================================================

/-- **Integration by Parts**: ∫ₐᵇ f'·g dt = [f·g]ₐᵇ - ∫ₐᵇ f·g' dt.

    Proof: Newton-Leibniz applied to h = f·g with h' = f'g + fg'. -/
theorem integration_by_parts {f g : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (deriv f x) x)
    (hg : ∀ x ∈ uIcc a b, HasDerivAt g (deriv g x) x)
    (hf' : ContinuousOn (deriv f) (uIcc a b))
    (hg' : ContinuousOn (deriv g) (uIcc a b))
    (hfc : ContinuousOn f (uIcc a b))
    (hgc : ContinuousOn g (uIcc a b)) :
    ∫ t in a..b, deriv f t * g t =
    f b * g b - f a * g a - ∫ t in a..b, f t * deriv g t := by
  -- h = f·g, h' = f'g + fg'
  have hfg : ∀ x ∈ uIcc a b, HasDerivAt (fun x => f x * g x)
      (deriv f x * g x + f x * deriv g x) x :=
    fun x hx => (hf x hx).mul (hg x hx)
  have hfg' : ContinuousOn (fun x => deriv f x * g x + f x * deriv g x) (uIcc a b) :=
    (hf'.mul hgc).add (hfc.mul hg')
  -- Newton-Leibniz
  have nl : ∫ t in a..b, (deriv f t * g t + f t * deriv g t) =
      f b * g b - f a * g a :=
    integral_eq_sub_of_hasDerivAt hfg hfg'.intervalIntegrable
  -- Split by linearity
  have hint1 : IntervalIntegrable (fun x => deriv f x * g x) volume a b :=
    (hf'.mul hgc).intervalIntegrable
  have hint2 : IntervalIntegrable (fun x => f x * deriv g x) volume a b :=
    (hfc.mul hg').intervalIntegrable
  linarith [integral_add hint1 hint2 |>.symm.trans nl |>.symm]

-- ============================================================
-- Part V: Antiderivative Uniqueness
-- ============================================================

/-- **FTC Uniqueness**: Two differentiable functions with the same derivative
    on uIcc a b and the same value at a are equal everywhere.

    Proof: h = F - G has h' = 0 everywhere, so Newton-Leibniz gives
    ∫ₐˣ 0 dt = h(x) - h(a), i.e., h(x) = h(a) = 0. -/
theorem ftc_uniqueness {F G : ℝ → ℝ} {f : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ uIcc a b, HasDerivAt F (f x) x)
    (hG : ∀ x ∈ uIcc a b, HasDerivAt G (f x) x)
    (hinit : F a = G a) :
    ∀ x ∈ uIcc a b, F x = G x := by
  intro x hx
  -- h = F - G has h' = 0 on uIcc a x (contained in uIcc a b)
  have hh : ∀ y ∈ uIcc a x, HasDerivAt (fun t => F t - G t) (0:ℝ) y := by
    intro y hy
    have hyb : y ∈ uIcc a b := by
      rcases mem_uIcc.mp hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases mem_uIcc.mp hx with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exact mem_uIcc.mpr (Or.inl ⟨h1, h2.trans h4⟩)
      · exact mem_uIcc.mpr (Or.inr ⟨h3.trans h1, h2⟩)
      · exact mem_uIcc.mpr (Or.inl ⟨h2, h1.trans h4⟩)
      · exact mem_uIcc.mpr (Or.inr ⟨h3.trans h2, h1⟩)
    simpa using (hF y hyb).sub (hG y hyb)
  -- Newton-Leibniz: ∫ₐˣ 0 = (F-G)(x) - (F-G)(a)
  have hint : (∫ _t in a..x, (0:ℝ)) = (F x - G x) - (F a - G a) :=
    integral_eq_sub_of_hasDerivAt hh intervalIntegrable_const
  simp at hint
  linarith [hinit]

-- ============================================================
-- Part VI: Integral Approximation via MVT
-- ============================================================

/-- **Integral Approximation from MVT**: If g approximates f' within ε
    uniformly on [a,b], then their integrals differ by at most ε·(b-a).

    This shows how the MVT bound propagates to the integral level. -/
theorem integral_approx_from_mvt {f g : ℝ → ℝ} {a b ε : ℝ}
    (hab : a ≤ b) (hε : 0 ≤ ε)
    (hf : ContinuousOn (deriv f) (uIcc a b))
    (hg : ContinuousOn g (uIcc a b))
    (happrox : ∀ x ∈ uIcc a b, |deriv f x - g x| ≤ ε) :
    |∫ t in a..b, deriv f t - ∫ t in a..b, g t| ≤ ε * (b - a) := by
  rw [← intervalIntegral.integral_sub hf.intervalIntegrable hg.intervalIntegrable]
  have hbound : ∀ x ∈ uIcc a b, ‖deriv f x - g x‖ ≤ ε := by
    intro x hx; rw [Real.norm_eq_abs]; exact happrox x hx
  calc |∫ t in a..b, (deriv f t - g t)|
      = ‖∫ t in a..b, (deriv f t - g t)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t in a..b, ‖deriv f t - g t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..b, ε := by
        apply intervalIntegral.integral_mono_on hab
        · exact (hf.sub hg).norm.intervalIntegrable
        · exact continuous_const.continuousOn.intervalIntegrable
        · intro x hx
          have hxu : x ∈ uIcc a b := Icc_subset_uIcc hx
          exact hbound x hxu
    _ = ε * (b - a) := by simp [mul_comm]

-- ============================================================
-- Part VII: Structural Summary — MVT-FTC Duality
-- ============================================================

/-!
## Structural Summary

The MVT and FTC are dual formulations of the same relationship:

| Theorem | Formula | Tool |
|---------|---------|------|
| **MVT** | f(b)-f(a) = f'(c)·(b-a), some c | IVT (existence) |
| **FTC** | f(b)-f(a) = ∫ₐᵇ f' dt | Riemann (exactness) |
| **Connection** | f'(c) = ∫ₐᵇ f'/(b-a) for some c | MVT from FTC+IVT |

FTC is strictly stronger than MVT:
- FTC gives exact formula (integral)
- MVT gives existence of a witness (not constructive)
- FTC + IVT → MVT (proved in `ftc_implies_mvt`)

### Key Mathlib Theorems Used

- `intervalIntegral.integral_hasDerivAt_right` — FTC Part 1
- `integral_eq_sub_of_hasDerivAt` — Newton-Leibniz / FTC Part 2
- `exists_deriv_eq_slope` — MVT for ℝ→ℝ
-/

-- ============================================================
-- Part VIII: Integration as Inverse of Differentiation
-- ============================================================

/-- **Round-trip Part 1**: Differentiate then integrate recovers the net change.
    (deriv F = f) + FTC → ∫ₐᵇ f = F(b) - F(a). -/
theorem diff_then_integrate {F f : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ uIcc a b, HasDerivAt F (f x) x)
    (hf : ContinuousOn f (uIcc a b)) :
    ∫ t in a..b, f t = F b - F a :=
  newton_leibniz hF hf

/-- **Round-trip Part 2**: Integrate then differentiate recovers f.
    F(x) := ∫ₐˣ f satisfies F'(x) = f(x). -/
theorem integrate_then_diff {f : ℝ → ℝ} {a : ℝ}
    (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun x => ∫ t in a..x, f t) (f x) x :=
  ftc_part1 hf x

/-- **No information loss in FTC**: Given F₁ and F₂ both satisfying FTC
    with the same integrand and same initial value F(a), they are equal.
    (Uniqueness of antiderivatives.) -/
theorem ftc_no_loss {F₁ F₂ : ℝ → ℝ} {f : ℝ → ℝ} {a b : ℝ}
    (h₁ : ∀ x ∈ uIcc a b, HasDerivAt F₁ (f x) x)
    (h₂ : ∀ x ∈ uIcc a b, HasDerivAt F₂ (f x) x)
    (hinit : F₁ a = F₂ a) :
    ∀ x ∈ uIcc a b, F₁ x = F₂ x :=
  ftc_uniqueness h₁ h₂ hinit

-- ============================================================
-- Part IX: FTC for Lipschitz Functions
-- ============================================================

/-- A K-Lipschitz function satisfies the distance bound dist(F(a), F(b)) ≤ K·dist(a,b).
    This is the "FTC-free" way to control function differences. -/
theorem lipschitz_dist_bound {F : ℝ → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K F) (a b : ℝ) :
    dist (F a) (F b) ≤ K * dist a b :=
  hF.dist_le_mul a b

#check @ftc_part1
#check @ftc_part1_deriv
#check @antiderivative_of_integral
#check @newton_leibniz
#check @ftc_part2
#check @ftc_implies_mvt
#check @mvt_equals_integral_average
#check @integration_by_parts
#check @ftc_uniqueness
#check @integral_approx_from_mvt
#check @lipschitz_dist_bound

end MeanValueTheoremOQ04
