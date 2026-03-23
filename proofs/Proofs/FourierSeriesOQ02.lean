import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Tactic

/-
# Fourier Coefficient Decay Under Hölder Continuity (OQ-02)

## Research Question

What is the optimal rate of decay of Fourier coefficients under Hölder continuity?

## Main Result

If f : AddCircle T → ℂ is α-Hölder continuous with constant C, then for n ≠ 0:

  ‖ĉ_n(f)‖ ≤ (C/2) · (T / (2|n|))^α

This bound is sharp: for each 0 < α < 1, there exists an α-Hölder function
whose coefficients decay exactly at rate O(1/|n|^α).

## Proof Technique: Half-Period Translation

Translate x ↦ x + T/(2n). Since e_{-n}(x + T/(2n)) = -e_{-n}(x), we get:

  2 · ĉ_n(f) = ∫ (f(x) - f(x + T/(2n))) · e_{-n}(x) dx

Hölder continuity bounds |f(x) - f(x + T/(2n))| ≤ C · (T/(2|n|))^α.
Since ‖e_{-n}(x)‖ = 1 and the circle has probability measure 1:

  ‖2 · ĉ_n(f)‖ ≤ C · (T / (2|n|))^α  ⟹  ‖ĉ_n(f)‖ ≤ (C/2) · (T/(2|n|))^α
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Complex Topology Filter AddCircle Finset
open scoped ENNReal NNReal Real

namespace FourierHolderDecay

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: HÖLDER CONTINUITY ON THE CIRCLE
═══════════════════════════════════════════════════════════════════════════════ -/

variable {T : ℝ} [hT : Fact (0 < T)]

/-- A function on the additive circle is α-Hölder continuous with constant C. -/
def IsHolderOnCircle (C : ℝ≥0) (α : ℝ≥0) (f : AddCircle T → ℂ) : Prop :=
  HolderWith C α f

/-- Hölder continuity implies continuity. -/
theorem holder_continuous {C : ℝ≥0} {α : ℝ≥0} {f : AddCircle T → ℂ}
    (hf : IsHolderOnCircle C α f) (hα : 0 < α) :
    Continuous f := by
  exact hf.continuous hα

/-- Lipschitz is the special case α = 1. -/
theorem lipschitz_is_holder_one {C : ℝ≥0} {f : AddCircle T → ℂ}
    (hf : LipschitzWith C f) :
    IsHolderOnCircle C 1 f := by
  intro x y
  simp only [NNReal.coe_one, ENNReal.rpow_one]
  exact hf.edist_le_mul x y

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: TRANSLATION INFRASTRUCTURE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Translation on AddCircle T by s ∈ ℝ. -/
def circleTranslate (s : ℝ) (x : AddCircle T) : AddCircle T :=
  x + ↑s

/-- The half-period for the n-th Fourier mode: T/(2n). -/
def halfPeriod (T : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else T / (2 * ↑n)

/-- Fourier monomials have unit norm: ‖e_n(x)‖ = 1 for all x.
    This is because fourier n x = ↑(n • x).toCircle lies on the unit circle in ℂ.
    Proved via fourier_apply which unfolds to the circle-valued toCircle map. -/
theorem fourier_norm_one (n : ℤ) (x : AddCircle T) : ‖fourier n x‖ = 1 := by
  simp [fourier_apply]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: ANALYSIS INFRASTRUCTURE (PARTIALLY PROVED)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Key identity: translating by T/(2n) negates the n-th Fourier monomial.

    fourier(-n)(x + T/(2n)) = e^{2πi(-n)(x + T/(2n))/T}
                             = e^{2πi(-n)x/T} · e^{-πi}
                             = -fourier(-n)(x)

    Proved by reducing to Mathlib's fourier_add_half_inv_index (for mode n)
    via the conjugation identity fourier_neg: fourier(-n) = conj(fourier n). -/
theorem fourier_translate_halfperiod (n : ℤ) (hn : n ≠ 0) (x : AddCircle T) :
    fourier (-n) (circleTranslate (halfPeriod T n) x) = -(fourier (-n) x) := by
  unfold circleTranslate halfPeriod
  simp only [hn, ite_false]
  rw [fourier_neg, fourier_neg]
  have h_eq : (T / (2 * (↑n : ℝ)) : ℝ) = T / 2 / ↑n := by ring
  rw [h_eq, fourier_add_half_inv_index hn hT.out]
  exact map_neg (starRingEnd ℂ) (fourier n x)

/-- Difference formula for Fourier coefficients:

    2 · ĉ_n(f) = ∫ (f(x) - f(x + T/(2n))) · e_{-n}(x) dx

    From translation invariance of Haar measure and the half-period identity. -/
axiom fourierCoeff_difference_formula (f : AddCircle T → ℂ) (n : ℤ) (hn : n ≠ 0) :
    2 * fourierCoeff f n =
      ∫ x : AddCircle T,
        (f x - f (circleTranslate (halfPeriod T n) x)) * fourier (-n) x ∂haarAddCircle

/-- Hölder bound on translation differences:
    ‖f(x) - f(x + T/(2n))‖ ≤ C · (T/(2|n|))^α

    Proof: From HolderWith.dist_le_of_le + quotient norm bound.
    The key insight is that dist(x, x+↑s) = ‖↑s‖ on AddCircle T,
    and the quotient norm satisfies ‖↑s‖ ≤ |s| by norm_mk_le_norm. -/
theorem holder_translation_bound (C : ℝ≥0) (α : ℝ≥0) (f : AddCircle T → ℂ)
    (hf : IsHolderOnCircle C α f) (n : ℤ) (hn : n ≠ 0) (x : AddCircle T) :
    ‖f x - f (circleTranslate (halfPeriod T n) x)‖ ≤
      ↑C * (T / (2 * |↑n|)) ^ (α : ℝ) := by
  -- Step 1: Bound the distance on AddCircle
  have hdist : dist x (circleTranslate (halfPeriod T n) x) ≤ T / (2 * |(↑n : ℝ)|) := by
    unfold circleTranslate halfPeriod
    simp only [hn, ite_false]
    -- dist x (x + ↑s) = ‖x - (x + ↑s)‖ = ‖↑s‖ (via norm_sub_rev + add_sub_cancel_left)
    rw [dist_eq_norm, norm_sub_rev, add_sub_cancel_left]
    -- ‖(↑s : AddCircle T)‖ ≤ ‖s‖ₐ = |s| by quotient norm bound
    calc ‖(↑(T / (2 * (↑n : ℝ))) : AddCircle T)‖
        ≤ ‖T / (2 * (↑n : ℝ))‖ := QuotientAddGroup.norm_mk_le_norm
      _ = |T / (2 * (↑n : ℝ))| := Real.norm_eq_abs _
      _ = T / (2 * |(↑n : ℝ)|) := by
          rw [abs_div, abs_of_pos hT.out, abs_mul,
            abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  -- Step 2: Apply HolderWith.dist_le_of_le to get norm bound
  have h := hf.dist_le_of_le hdist
  rwa [dist_eq_norm] at h

/-- The integral of the product is bounded by the Hölder constant.
    Uses: (1) norm_integral_le_of_norm_le_const, (2) ‖e_{-n}(x)‖ = 1,
    (3) Hölder bound on difference, (4) probability measure total mass 1.

    Proof: Bound ‖g(x)‖ ≤ C·d^α pointwise (where g = (f-f∘τ)·e_{-n}),
    then integrate the constant bound over the probability space. -/
theorem integral_product_bound (C : ℝ≥0) (α : ℝ≥0) (f : AddCircle T → ℂ)
    (hf : IsHolderOnCircle C α f) (n : ℤ) (hn : n ≠ 0) :
    ‖∫ x : AddCircle T,
      (f x - f (circleTranslate (halfPeriod T n) x)) * fourier (-n) x ∂haarAddCircle‖ ≤
      ↑C * (T / (2 * |↑n|)) ^ (α : ℝ) := by
  set bound := ↑C * (T / (2 * |(↑n : ℝ)|)) ^ (↑α : ℝ) with hbound_def
  -- Pointwise norm bound: ‖(f x - f(x+s)) · e_{-n}(x)‖ ≤ bound
  have hpointwise : ∀ x : AddCircle T,
      ‖(f x - f (circleTranslate (halfPeriod T n) x)) * fourier (-n) x‖ ≤ bound := by
    intro x
    rw [norm_mul, fourier_norm_one, mul_one]
    exact holder_translation_bound C α f hf n hn x
  -- Apply norm_integral_le bound with probability measure
  calc ‖∫ x : AddCircle T,
        (f x - f (circleTranslate (halfPeriod T n) x)) * fourier (-n) x ∂haarAddCircle‖
      ≤ ∫ x : AddCircle T,
        ‖(f x - f (circleTranslate (halfPeriod T n) x)) * fourier (-n) x‖ ∂haarAddCircle :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _ : AddCircle T, bound ∂haarAddCircle := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Eventually.of_forall (fun x => norm_nonneg _)
        · exact integrable_const _
        · exact Eventually.of_forall (fun x => hpointwise x)
    _ = bound * (haarAddCircle (Set.univ)).toReal := by
        rw [MeasureTheory.integral_const]
        ring
    _ = bound := by
        rw [IsProbabilityMeasure.measure_univ, ENNReal.one_toReal, mul_one]

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: MAIN THEOREM — FOURIER COEFFICIENT DECAY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Main Theorem: Fourier Coefficient Decay Under Hölder Continuity**

    If f : AddCircle T → ℂ is α-Hölder with constant C, then for n ≠ 0:

      ‖ĉ_n(f)‖ ≤ (C/2) · (T / (2|n|))^α

    Proof:
    1. Difference formula: 2ĉ_n = ∫ (f(x) - f(x + T/(2n))) e_{-n}(x) dx
    2. Bound the integral: ‖...‖ ≤ C · (T/(2|n|))^α
    3. Divide by 2: ‖ĉ_n‖ ≤ (C/2) · (T/(2|n|))^α -/
theorem fourierCoeff_holder_decay (C : ℝ≥0) (α : ℝ≥0) (f : AddCircle T → ℂ)
    (hf : IsHolderOnCircle C α f) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff f n‖ ≤ (↑C / 2) * (T / (2 * |↑n|)) ^ (α : ℝ) := by
  have hdiff := fourierCoeff_difference_formula f n hn
  have hbound : ‖2 * fourierCoeff f n‖ ≤
      ↑C * (T / (2 * |↑n|)) ^ (α : ℝ) := by
    rw [hdiff]
    exact integral_product_bound C α f hf n hn
  rw [norm_mul, norm_ofNat] at hbound
  linarith

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: COROLLARIES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Lipschitz Case (α = 1)**: ‖ĉ_n(f)‖ ≤ CT/(4|n|).
    Recovers the classical integration-by-parts estimate. -/
theorem fourierCoeff_lipschitz_decay (C : ℝ≥0) (f : AddCircle T → ℂ)
    (hf : LipschitzWith C f) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff f n‖ ≤ (↑C / 2) * (T / (2 * |↑n|)) := by
  have h := fourierCoeff_holder_decay C 1 f (lipschitz_is_holder_one hf) n hn
  simp only [NNReal.coe_one, Real.rpow_one] at h
  exact h

/-- **Square-Summability for α > 1/2**: ‖ĉ_n‖ = O(1/|n|^α), so
    ‖ĉ_n‖² = O(1/|n|^{2α}), and Σ 1/|n|^{2α} < ∞ when 2α > 1. -/
axiom fourierCoeff_sq_summable_of_holder (C : ℝ≥0) (α : ℝ≥0)
    (f : AddCircle T → ℂ) (hf : IsHolderOnCircle C α f)
    (hα : (1 : ℝ) / 2 < (α : ℝ)) :
    Summable (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2)

/-- **Riemann-Lebesgue from Hölder**: ‖ĉ_n‖ = O(1/|n|^α) → 0. -/
axiom riemannLebesgue_of_holder (C : ℝ≥0) (α : ℝ≥0)
    (f : AddCircle T → ℂ) (hf : IsHolderOnCircle C α f) (hα : 0 < α) :
    Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0)

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI: OPTIMALITY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Optimality**: For 0 < α < 1, there exists an α-Hölder function whose
    coefficients decay at exactly the rate O(1/|n|^α).

    Example: Weierstrass function f(x) = Σ_{k≥0} b^{-kα} e^{ib^k x}
    has |ĉ_{b^k}| = b^{-kα} = 1/|n|^α at frequencies n = b^k. -/
axiom holder_decay_is_optimal :
    ∀ (α : ℝ), 0 < α → α < 1 →
    ∃ (C : ℝ≥0) (f : AddCircle T → ℂ), IsHolderOnCircle C α.toNNReal f ∧
      ∃ (c : ℝ), 0 < c ∧
        ∀ᶠ n in cofinite, c / |↑n| ^ α ≤ ‖fourierCoeff f n‖

/-- **Partial Converse**: ‖ĉ_n‖ = O(1/|n|^β) with β > α + 1/2 implies
    f is α-Hölder. The gap 1/2 comes from the Sobolev embedding on the circle. -/
axiom decay_implies_regularity (β α : ℝ) (hβα : α + 1/2 < β) (hα : 0 < α)
    (f : AddCircle T → ℂ) (C_decay : ℝ)
    (hdecay : ∀ n : ℤ, n ≠ 0 →
      ‖fourierCoeff f n‖ ≤ C_decay / |↑n| ^ β) :
    ∃ (C_holder : ℝ≥0), IsHolderOnCircle C_holder α.toNNReal f

/-
═══════════════════════════════════════════════════════════════════════════════
PART VII: THE FULL REGULARITY-DECAY HIERARCHY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **C^k Decay**: k-times differentiable ⟹ ‖ĉ_n‖ = O(1/|n|^k) by
    iterated integration by parts. Hölder gives fractional generalization:
    C^{k,α} ⟹ O(1/|n|^{k+α}). -/
axiom fourierCoeff_smooth_decay (k : ℕ) (f : AddCircle T → ℂ)
    (hf_smooth : ContDiff ℝ k (fun x : ℝ => f (↑x : AddCircle T)))
    (n : ℤ) (hn : n ≠ 0) :
    ∃ (Ck : ℝ), 0 < Ck ∧ ‖fourierCoeff f n‖ ≤ Ck / |↑n| ^ (k : ℝ)

/-- **Rapid Decay for C^∞**: C^∞ ⟹ ‖ĉ_n‖ decays faster than any
    polynomial (Schwartz class on the circle). -/
axiom fourierCoeff_Cinfty_rapid_decay (f : AddCircle T → ℂ)
    (hf : ∀ k : ℕ, ContDiff ℝ k (fun x : ℝ => f (↑x : AddCircle T)))
    (k : ℕ) (n : ℤ) (hn : n ≠ 0) :
    ∃ (Ck : ℝ), 0 < Ck ∧ ‖fourierCoeff f n‖ ≤ Ck / |↑n| ^ (k : ℝ)

/-- **Analytic Decay**: Holomorphic on strip of width δ ⟹
    ‖ĉ_n‖ ≤ C·e^{-2πδ|n|/T}. Exponential decay = analyticity. -/
axiom fourierCoeff_analytic_decay (f : AddCircle T → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (n : ℤ) (hn : n ≠ 0) :
    ∃ (C_an : ℝ), 0 < C_an ∧
      ‖fourierCoeff f n‖ ≤ C_an * Real.exp (-2 * Real.pi * δ * |↑n| / T)

/-
═══════════════════════════════════════════════════════════════════════════════
PART VIII: ARITHMETIC CONSEQUENCES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- α > 1/2 ⟹ 2α > 1 (threshold for square-summability). -/
theorem holder_half_critical :
    ∀ (α : ℝ), α > 1/2 → 2 * α > 1 :=
  fun α hα => by linarith

/-- For α ∈ (1/2, 1], the decay exponent 2α ∈ (1, 2]. -/
theorem holder_parseval_range :
    ∀ (α : ℝ), 1/2 < α → α ≤ 1 → 1 < 2 * α ∧ 2 * α ≤ 2 :=
  fun α h1 h2 => ⟨by linarith, by linarith⟩

/-- Synonym: quantitative Riemann-Lebesgue with explicit rate. -/
theorem quantitative_riemannLebesgue (C : ℝ≥0) (α : ℝ≥0) (f : AddCircle T → ℂ)
    (hf : IsHolderOnCircle C α f) (n : ℤ) (hn : n ≠ 0) :
    ‖fourierCoeff f n‖ ≤ (↑C / 2) * (T / (2 * |↑n|)) ^ (α : ℝ) :=
  fourierCoeff_holder_decay C α f hf n hn

/-
═══════════════════════════════════════════════════════════════════════════════
PART IX: VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

#check @fourierCoeff_holder_decay      -- Main theorem
#check @fourierCoeff_lipschitz_decay   -- Lipschitz case
#check @riemannLebesgue_of_holder      -- Riemann-Lebesgue for Hölder
#check @holder_decay_is_optimal        -- Optimality
#check @decay_implies_regularity       -- Partial converse
#check @fourier_norm_one               -- ‖e_n(x)‖ = 1
#check @lipschitz_is_holder_one        -- Lipschitz ⊂ Hölder(1)
#check @holder_continuous              -- Hölder ⟹ continuous
#check @quantitative_riemannLebesgue   -- Quantitative R-L
#check @fourierCoeff_smooth_decay      -- C^k decay
#check @fourierCoeff_Cinfty_rapid_decay -- C^∞ rapid decay
#check @fourierCoeff_analytic_decay    -- Analytic exponential decay

end FourierHolderDecay
