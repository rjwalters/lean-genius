/-
Central Limit Theorem OQ-03-OQ-01: Gnedenko-Kolmogorov Domain of Attraction Classification

Research problem: central-limit-theorem-oq-03-oq-01
Parent proof: CentralLimitTheoremOQ03.lean (categorical convolution structure)

This file extends the Gnedenko-Kolmogorov framework with additional properties
of slowly varying functions and connections to the parent OQ-03's categorical
perspective on convolution.

Key contributions:
- Slowly varying function algebra (products, bounded perturbations)
- Regular variation closure properties
- Bridge between OQ-03's ProbMeasure-based domain of attraction and
  GnedenkoKolmogorov's characteristic function formulation

NOTE: Most of the domain of attraction theory is in GnedenkoKolmogorov.lean
(created for central-limit-theorem-oq-01-oq-01). This file adds algebraic
properties of the supporting infrastructure.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real Filter

namespace CentralLimitTheoremOQ03OQ01

-- ============================================================================
-- § 1. Slowly Varying Functions — Algebra
-- ============================================================================

/-- A function L : ℝ → ℝ is slowly varying at infinity if
    L(tx)/L(x) → 1 as x → ∞ for all t > 0. -/
def IsSlowlyVarying (L : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t →
    Filter.Tendsto (fun x => L (t * x) / L x) Filter.atTop (nhds 1)

/-- Constants are slowly varying. -/
theorem isSlowlyVarying_const (c : ℝ) (hc : c ≠ 0) : IsSlowlyVarying (fun _ => c) := by
  intro t _
  simp [div_self hc]

/-- The product of two slowly varying functions is slowly varying. -/
theorem isSlowlyVarying_mul {L₁ L₂ : ℝ → ℝ} (h₁ : IsSlowlyVarying L₁)
    (h₂ : IsSlowlyVarying L₂) :
    IsSlowlyVarying (fun x => L₁ x * L₂ x) := by
  intro t ht
  -- L₁(tx)L₂(tx)/(L₁(x)L₂(x)) = (L₁(tx)/L₁(x)) · (L₂(tx)/L₂(x))
  -- The quotient factors, and each factor → 1, so the product → 1·1 = 1
  have : (fun x => L₁ (t * x) * L₂ (t * x) / (L₁ x * L₂ x)) =
      (fun x => (L₁ (t * x) / L₁ x) * (L₂ (t * x) / L₂ x)) := by
    ext x; ring
  rw [this]
  have := (h₁ t ht).mul (h₂ t ht)
  simp [mul_one] at this
  exact this

/-- If L is slowly varying and c ≠ 0, then c · L is slowly varying. -/
theorem isSlowlyVarying_const_mul {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (c : ℝ) (hc : c ≠ 0) :
    IsSlowlyVarying (fun x => c * L x) := by
  intro t ht
  have : (fun x => c * L (t * x) / (c * L x)) = (fun x => L (t * x) / L x) := by
    ext x; field_simp
  rw [this]
  exact hL t ht

/-- The reciprocal of a slowly varying function is slowly varying
    (when eventually nonzero). -/
theorem isSlowlyVarying_inv {L : ℝ → ℝ} (hL : IsSlowlyVarying L) :
    IsSlowlyVarying (fun x => (L x)⁻¹) := by
  intro t ht
  have : (fun x => (L (t * x))⁻¹ / (L x)⁻¹) = (fun x => L x / L (t * x)) := by
    ext x; simp [div_eq_mul_inv, inv_inv]
  rw [this]
  -- L(x)/L(tx) → 1/1 = 1 since L(tx)/L(x) → 1
  have h := hL t ht
  -- Use that if f(x) → 1, then 1/f(x) → 1
  have := h.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simp [inv_one] at this
  -- Need to show L(x)/L(tx) → 1, which is the reciprocal of L(tx)/L(x) → 1
  convert this using 1
  ext x; ring

-- ============================================================================
-- § 2. Regular Variation — Properties
-- ============================================================================

/-- A function f is regularly varying with index -α if
    f(x) = x^(-α) · L(x) for some slowly varying L. -/
def IsRegularlyVarying (f : ℝ → ℝ) (α : ℝ) : Prop :=
  ∃ L : ℝ → ℝ, IsSlowlyVarying L ∧
    ∀ᶠ x in Filter.atTop, f x = x ^ (-α) * L x

/-- A regularly varying function with index 0 is slowly varying. -/
theorem isRegularlyVarying_zero_iff_slowlyVarying {f : ℝ → ℝ}
    (hf_ev : ∀ᶠ x in Filter.atTop, f x ≠ 0) :
    IsRegularlyVarying f 0 ↔ IsSlowlyVarying f := by
  constructor
  · rintro ⟨L, hL, hev⟩
    intro t ht
    -- f(tx)/f(x) = (tx)^0 · L(tx) / (x^0 · L(x)) = L(tx)/L(x) → 1
    have : ∀ᶠ x in Filter.atTop, f (t * x) / f x = L (t * x) / L x := by
      filter_upwards [hev, hev.comp_tendsto (tendsto_const_mul_atTop_of_pos ht tendsto_id)]
        with x hfx hftx
      rw [hfx, hftx]
      simp [rpow_zero]
    exact (Filter.Tendsto.congr' this.symm (hL t ht))
  · intro hf
    exact ⟨f, hf, by filter_upwards with x; simp [rpow_zero]⟩

-- ============================================================================
-- § 3. Stability Index Determines Tail Behavior
-- ============================================================================

/-- The stability index α is unique: if the same characteristic function
    is α-stable and β-stable (with α, β ∈ (0, 2]), then α = β.

    This follows from the form of the stable characteristic function:
    exp(-c|t|^α) determines α from the behavior at t → 0. -/
theorem stability_index_unique (φ : ℝ → ℂ) (α β : ℝ)
    (hα : 0 < α) (hα2 : α ≤ 2) (hβ : 0 < β) (hβ2 : β ≤ 2)
    (hsα : ∀ n : ℕ, 0 < n → ∀ t : ℝ, (φ (t / (n : ℝ) ^ (1 / α))) ^ n = φ t)
    (hsβ : ∀ n : ℕ, 0 < n → ∀ t : ℝ, (φ (t / (n : ℝ) ^ (1 / β))) ^ n = φ t)
    (hφ_nontrivial : φ 1 ≠ 0) :
    α = β := by
  -- From the stability equations with n = 2:
  -- [φ(t/2^(1/α))]^2 = φ(t)  and  [φ(t/2^(1/β))]^2 = φ(t)
  -- So φ(t/2^(1/α)) = ±φ(t/2^(1/β))
  -- Iterating and using continuity arguments determines the exponent uniquely.
  -- Full proof requires complex analysis of characteristic functions.
  sorry

-- ============================================================================
-- § 4. Connection to OQ-03's Categorical Framework
-- ============================================================================

/-
## Bridge to Parent OQ-03

The parent file CentralLimitTheoremOQ03.lean defines:
- ProbMeasure: probability measures on ℝ
- convolution: operation on ProbMeasure
- InDomainOfAttraction: domain of attraction of the Gaussian (α=2)

This file and GnedenkoKolmogorov.lean generalize to all α:
- InSymmetricDomainOfAttraction: domain of attraction of any α-stable law
- The GK theorem classifies all possible limit distributions

The connection:
  OQ-03.InDomainOfAttraction(μ)  ↔  GK.InSymmetricDomainOfAttraction(φ_μ, 2)

That is, OQ-03's domain of attraction for the Gaussian is precisely the
α=2 case of the general Gnedenko-Kolmogorov classification.

The categorical perspective (OQ-03) emphasizes the monoid structure:
  (ProbMeasure, convolution, δ₀) is a commutative monoid.
  The CLT says the Gaussian is an "attractor" under normalization.

The GK perspective adds:
  There are exactly the α-stable distributions (α ∈ (0,2]) as possible
  attractors, and the tail behavior P(|X| > x) ~ x^(-α) · L(x)
  determines which attractor a distribution converges to.
-/

-- ============================================================================
-- § 5. Domain of Attraction Hierarchy
-- ============================================================================

/-- A simplified symmetric domain of attraction concept, matching GK's framework
    but stated more concretely for reference. -/
def InDomainOfGaussian (φ : ℝ → ℂ) : Prop :=
  ∃ a : ℕ → ℝ,
    (∀ n, 0 < n → 0 < a n) ∧
    ∀ t : ℝ, Filter.Tendsto
      (fun n => (φ (t / a n)) ^ n)
      Filter.atTop (nhds (Complex.exp (↑(-(t^2 : ℝ)))))

/-- A distribution with characteristic function exp(-c·t²) (Gaussian with
    variance parameter c) is in the domain of the standard Gaussian. -/
theorem gaussian_family_in_domain (c : ℝ) (hc : 0 < c) :
    InDomainOfGaussian (fun t => Complex.exp (↑(-(c * t^2 : ℝ)))) := by
  refine ⟨fun n => Real.sqrt (c * n), ?_, ?_⟩
  · intro n hn
    exact Real.sqrt_pos_of_pos (mul_pos hc (Nat.cast_pos.mpr hn))
  · intro t
    -- [exp(-c(t/√(cn))²)]^n = [exp(-t²/n)]^n = exp(-t²)
    simp only [Complex.ofReal_neg, Complex.ofReal_mul]
    sorry

#check @isSlowlyVarying_mul
#check @isSlowlyVarying_inv
#check @isRegularlyVarying_zero_iff_slowlyVarying

end CentralLimitTheoremOQ03OQ01
