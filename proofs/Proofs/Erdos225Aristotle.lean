/-
  Aristotle targets for Erdős Problem #225
  Routine supporting lemmas for automated proof search.
  See Erdos225Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely provable from Mathlib
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib

namespace Erdos225Aristotle

open MeasureTheory Complex

/- ## Basic definitions (mirrored from Erdos225Problem.lean) -/

def TrigPoly (n : ℕ) := Fin (n + 1) → ℂ

noncomputable def TrigPoly.eval (p : TrigPoly n) (θ : ℝ) : ℂ :=
  ∑ k : Fin (n + 1), p k * Complex.exp (Complex.I * k * θ)

def HasUnitCircleRoots (p : TrigPoly n) : Prop :=
  ∀ z : ℂ, (∑ k : Fin (n + 1), p k * z ^ (k : ℕ)) = 0 → ‖z‖ = 1

def Nonconstant (p : TrigPoly n) : Prop :=
  ∃ z : ℂ, (∑ k : Fin (n + 1), p k * z ^ (k : ℕ)) = 0

/- ## Routine lemmas for Aristotle -/

/-- The constant polynomial 1 has no roots, so is not Nonconstant. -/
theorem constant_one_not_nonconstant :
    ¬ Nonconstant (fun (_ : Fin 1) => (1 : ℂ)) := by
  intro ⟨z, hz⟩
  simp [Fin.sum_univ_one] at hz

/-- Unit circle points have norm 1 (basic Mathlib fact). -/
theorem exp_on_unit_circle (θ : ℝ) :
    ‖Complex.exp (Complex.I * ↑θ)‖ = 1 := by
  rw [Complex.norm_exp_ofReal_mul_I]

/-- The norm of e^(iθ) - e^(iφ) equals 2|sin((θ-φ)/2)|.
    Proof via Euler's formula + Pythagorean identity + cos double angle. -/
theorem norm_exp_diff (θ φ : ℝ) :
    ‖Complex.exp (Complex.I * ↑θ) - Complex.exp (Complex.I * ↑φ)‖ =
    2 * |Real.sin ((θ - φ) / 2)| := by
  -- Rewrite I*θ as θ*I for Euler's formula compatibility
  rw [show Complex.I * (↑θ : ℂ) = ↑θ * Complex.I from mul_comm _ _,
      show Complex.I * (↑φ : ℂ) = ↑φ * Complex.I from mul_comm _ _]
  -- Apply Euler's formula: exp(x*I) = cos(x) + sin(x)*I
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  -- Simplify the difference to ↑(cos θ - cos φ) + ↑(sin θ - sin φ) * I
  have h_diff : (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I) -
      (↑(Real.cos φ) + ↑(Real.sin φ) * Complex.I) =
      ↑(Real.cos θ - Real.cos φ) + ↑(Real.sin θ - Real.sin φ) * Complex.I := by
    push_cast; ring
  rw [h_diff]
  -- Apply ‖a + b*I‖ = √(a² + b²) for real a, b
  rw [Complex.norm_add_mul_I]
  -- Show the radicand equals (2|sin((θ-φ)/2)|)²
  have h_sq : (Real.cos θ - Real.cos φ) ^ 2 + (Real.sin θ - Real.sin φ) ^ 2 =
      (2 * |Real.sin ((θ - φ) / 2)|) ^ 2 := by
    rw [mul_pow, sq_abs]
    -- Target: (cos θ - cos φ)² + (sin θ - sin φ)² = 4 * sin((θ-φ)/2)²
    -- This is a linear combination of: Pythagorean (×2), cos_sub, cos_two_mul, Pythagorean for half
    have h1 := Real.sin_sq_add_cos_sq θ
    have h2 := Real.sin_sq_add_cos_sq φ
    have h3 := Real.cos_sub θ φ
    have h4 := Real.cos_two_mul ((θ - φ) / 2)
    have h5 : 2 * ((θ - φ) / 2) = θ - φ := by ring
    rw [h5] at h4
    have h6 := Real.sin_sq_add_cos_sq ((θ - φ) / 2)
    -- Target = 1·h1 + 1·h2 + 2·h3 - 2·h4 - 4·h6 by ring expansion
    linear_combination h1 + h2 + 2 * h3 - 2 * h4 - 4 * h6
  rw [h_sq, Real.sqrt_sq (by positivity)]

/-- For a degree-1 polynomial p(z) = c₀ + c₁z with c₁ ≠ 0,
    HasUnitCircleRoots implies |c₀| = |c₁|. -/
theorem unit_circle_root_coeff_norm (c₀ c₁ : ℂ) (hc₁ : c₁ ≠ 0)
    (hroot : ∀ z : ℂ, c₀ + c₁ * z = 0 → ‖z‖ = 1) :
    ‖c₀‖ = ‖c₁‖ := by
  -- The unique root is z = -c₀/c₁, and ‖z‖ = 1 gives ‖c₀‖ = ‖c₁‖
  have hroot1 := hroot (-c₀ / c₁) (by field_simp; ring)
  rwa [norm_div, norm_neg, div_eq_one_iff_eq (by rwa [norm_ne_zero_iff])] at hroot1

/-- If |α| = 1 then |−α| = 1. -/
theorem norm_neg_of_norm_one (α : ℂ) (hα : ‖α��� = 1) :
    ‖-α��� = 1 := by
  rw [norm_neg]; exact hα

/-- The supremum of |α + e^(iθ)| for |α| = 1 is 2. -/
theorem sup_norm_sum_exp (α : ℂ) (hα : ‖α‖ = 1) :
    ⨆ θ : Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖α + Complex.exp (Complex.I * ↑(θ : ℝ))‖ = 2 := by
  sorry

/-- ∫₀²π |sin(θ/2)| dθ = 4 (routine calculus). -/
theorem integral_abs_sin_half :
    ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), |Real.sin (θ / 2)| = 4 := by
  sorry

/-- 2π > 4, i.e., the constant polynomial's L¹ norm exceeds the bound. -/
theorem two_pi_gt_four : (2 : ℝ) * Real.pi > 4 := by
  linarith [Real.pi_gt_three]

end Erdos225Aristotle
