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
  sorry

/-- The norm of e^(iθ) - e^(iφ) equals 2|sin((θ-φ)/2)|. -/
theorem norm_exp_diff (θ φ : ℝ) :
    ‖Complex.exp (Complex.I * ↑θ) - Complex.exp (Complex.I * ↑φ)‖ =
    2 * |Real.sin ((θ - φ) / 2)| := by
  sorry

/-- For a degree-1 polynomial p(z) = c₀ + c₁z with c₁ ≠ 0,
    HasUnitCircleRoots implies |c₀| = |c₁|. -/
theorem unit_circle_root_coeff_norm (c₀ c₁ : ℂ) (hc₁ : c₁ ≠ 0)
    (hroot : ∀ z : ℂ, c₀ + c₁ * z = 0 → ‖z‖ = 1) :
    ‖c₀‖ = ‖c₁‖ := by
  sorry

/-- If |α| = 1 then |−α| = 1. -/
theorem norm_neg_of_norm_one (α : ℂ) (hα : ‖α��� = 1) :
    ‖-α��� = 1 := by
  sorry

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
  sorry

end Erdos225Aristotle
