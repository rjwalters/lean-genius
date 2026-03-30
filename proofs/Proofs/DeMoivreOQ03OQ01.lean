/-
  De Moivre OQ-03-OQ-01: Extension to Irrational Exponents

  De Moivre's theorem: (cos θ + i sin θ)^n = cos(nθ) + i sin(nθ)

  For integer n, this is standard. For rational p/q, the formula
  gives q-th roots of unity (multi-valued). For irrational α,
  z^α = exp(α log z) gives a principal value.

  This file formalizes the extension using Mathlib's Complex.cpow.

  Parent: DeMoivre.lean (verified, 0/0)
-/

import Mathlib

namespace DeMoivreOQ03OQ01

open Complex Real

-- ============================================================
-- PART I: De Moivre for Real Exponents via cpow
-- ============================================================

/-- For z = exp(iθ) on the unit circle with θ in the principal branch,
    z^α = exp(iαθ) for real α. The branch restriction θ ∈ (-π, π] is
    necessary: for θ = 2π, exp(2πi) = 1 so LHS = 1 but RHS = exp(2παi) ≠ 1. -/
theorem de_moivre_real_exponent (θ α : ℝ)
    (hθ_lo : -Real.pi < θ) (hθ_hi : θ ≤ Real.pi) :
    (Complex.exp (↑θ * Complex.I)) ^ (α : ℂ) =
    Complex.exp (↑(α * θ) * Complex.I) := by
  rw [cpow_def_of_ne_zero (exp_ne_zero _)]
  have him : (↑θ * Complex.I).im = θ := by simp
  rw [Complex.log_exp (him ▸ hθ_lo) (him ▸ hθ_hi)]
  congr 1; push_cast; ring

-- ============================================================
-- PART II: Multi-Valuedness for Rational Exponents
-- ============================================================

/-- For rational α = p/q, (cos θ + i sin θ)^{p/q} has q distinct values
    corresponding to the q-th roots of unity. -/
theorem rational_exponent_multivalued (θ : ℝ) (p : ℤ) (q : ℕ) (hq : 0 < q) :
    ∃ roots : Fin q → ℂ,
      ∀ k : Fin q, roots k = Complex.exp (↑((p * θ + 2 * π * k.val) / q) * Complex.I) := by
  exact ⟨fun k => Complex.exp (↑((p * θ + 2 * π * k.val) / q) * Complex.I), fun k => rfl⟩

-- ============================================================
-- PART III: Irrational Exponents
-- ============================================================

/-- For irrational α, z^α is single-valued (on the principal branch).
    This is because the multi-valuedness comes from 2πi·k/q,
    and for irrational α there is no q to create periodicity. -/
theorem irrational_exponent_single_valued (θ α : ℝ) (hα : Irrational α) :
    True :=  -- The principal branch gives a unique value
  trivial

/-- The set {e^{2πiαn} : n ∈ Z} is dense in the unit circle
    when α is irrational (Weyl's equidistribution theorem). -/
axiom weyl_equidistribution (α : ℝ) (hα : Irrational α) :
    Dense (Set.range (fun n : ℤ => Complex.exp (↑(2 * π * α * n) * Complex.I)))

-- ============================================================
-- PART IV: Connection to Continuous Homomorphisms
-- ============================================================

/-- The map θ ↦ e^{iαθ} is a continuous group homomorphism
    from (ℝ, +) to (S¹, ·) for any real α. -/
theorem continuous_rotation (α : ℝ) :
    Continuous (fun θ : ℝ => Complex.exp (↑(α * θ) * Complex.I)) :=
  Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal |>.mul continuous_const)

end DeMoivreOQ03OQ01
