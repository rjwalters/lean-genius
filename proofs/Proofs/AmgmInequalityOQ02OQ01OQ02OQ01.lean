/-
  Full Newton-Girard Recurrence for Symmetric Polynomials

  Open Question (amgm-inequality-oq-02-oq-01-oq-02-oq-01):
  Prove the general Newton-Girard recurrence connecting power sums
    pₖ = Σ xᵢᵏ
  and elementary symmetric polynomials
    eₖ = Σ_{i₁<...<iₖ} xᵢ₁...xᵢₖ
  for all k ≥ 1.

  Mathlib provides MvPolynomial.psum_eq_mul_esymm_sub_sum which states:
    pₙ = (-1)^(n+1) · n · eₙ - Σ_{i<n-1} (-1)^i · eᵢ₊₁ · pₙ₋₁₋ᵢ

  Corollaries (k = 1, 2, 3):
    p₁ = e₁
    p₂ = e₁² − 2·e₂
    p₃ = e₁·p₂ − e₂·p₁ + 3·e₃

  Status: WIP — sorries remain for the explicit corollary derivations.
  Axioms: 0, Sorries: 3
  Tags: algebra, symmetric-functions, newton-girard, power-sums, mv-polynomial
-/

import Mathlib

namespace AMGMInequalityOQ02OQ01OQ02OQ01

open MvPolynomial Finset BigOperators

variable (σ : Type*) (R : Type*) [CommRing R] [Fintype σ]

-- ============================================================
-- Main Theorem: Newton-Girard Recurrence (via Mathlib)
-- ============================================================

/-- **Newton-Girard Recurrence** (from Mathlib):
    For n ≥ 1, the power sum pₙ satisfies:
      pₙ = (-1)^(n+1) · n · eₙ − Σ_{0≤i<n-1} (-1)^i · eᵢ₊₁ · pₙ₋₁₋ᵢ

    This is `MvPolynomial.psum_eq_mul_esymm_sub_sum` from Mathlib. -/
theorem newton_girard_recurrence (n : ℕ) (hn : n ≠ 0) :
    psum σ R n =
      (-1) ^ (n + 1) * (n : R) * esymm σ R n -
      ∑ i ∈ range (n - 1), (-1) ^ i * (esymm σ R (i + 1) * psum σ R (n - 1 - i)) :=
  MvPolynomial.psum_eq_mul_esymm_sub_sum σ R n hn

-- ============================================================
-- Corollary 1: p₁ = e₁
-- ============================================================

/-- **Newton-Girard k=1**: The first power sum equals the first elementary symmetric polynomial:
      p₁ = e₁ -/
theorem psum_one_eq_esymm_one :
    psum σ R 1 = esymm σ R 1 := by
  sorry

-- ============================================================
-- Corollary 2: p₂ = e₁² − 2·e₂
-- ============================================================

/-- **Newton-Girard k=2**: The second power sum satisfies:
      p₂ = e₁² − 2·e₂
    Equivalently: Σ xᵢ² = (Σ xᵢ)² − 2·Σ_{i<j} xᵢxⱼ. -/
theorem psum_two_eq :
    psum σ R 2 = esymm σ R 1 ^ 2 - 2 * esymm σ R 2 := by
  sorry

-- ============================================================
-- Corollary 3: p₃ = e₁·p₂ − e₂·p₁ + 3·e₃
-- ============================================================

/-- **Newton-Girard k=3**: The third power sum satisfies:
      p₃ = e₁·p₂ − e₂·p₁ + 3·e₃ -/
theorem psum_three_eq :
    psum σ R 3 =
      esymm σ R 1 * psum σ R 2 - esymm σ R 2 * psum σ R 1 + 3 * esymm σ R 3 := by
  sorry

end AMGMInequalityOQ02OQ01OQ02OQ01
