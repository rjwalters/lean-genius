/-
  Full Newton-Girard Recurrence for Symmetric Polynomials

  Open Question (amgm-inequality-oq-02-oq-01-oq-02-oq-01):
  Prove the general Newton-Girard recurrence connecting power sums
    pₖ = Σ xᵢᵏ
  and elementary symmetric polynomials
    eₖ = Σ_{i₁<...<iₖ} xᵢ₁...xᵢₖ
  for all k ≥ 1.

  Mathlib provides MvPolynomial.psum_eq_mul_esymm_sub_sum which states:
    pₙ = (-1)^(n+1) · n · eₙ - Σ_{0<i<n} (-1)^i · eᵢ · pₙ₋ᵢ
  (sum over antidiagonal pairs (i,j) with i+j=n, 0<i<n)

  Corollaries (k = 1, 2, 3):
    p₁ = e₁
    p₂ = e₁² − 2·e₂
    p₃ = e₁·p₂ − e₂·p₁ + 3·e₃

  Status: Complete — all corollaries proved via Mathlib Newton-Girard recurrence.
  Axioms: 0, Sorries: 0
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
      pₙ = (-1)^(n+1) · n · eₙ − Σ_{0<i<n} (-1)^i · eᵢ · pₙ₋ᵢ
    where the sum runs over antidiagonal pairs (i,j) with i+j=n and 0<i<n.

    This is `MvPolynomial.psum_eq_mul_esymm_sub_sum` from Mathlib. -/
theorem newton_girard_recurrence (n : ℕ) (hn : 0 < n) :
    psum σ R n =
      (-1) ^ (n + 1) * (n : MvPolynomial σ R) * esymm σ R n -
      ∑ a ∈ antidiagonal n with a.1 ∈ Set.Ioo 0 n,
        (-1) ^ a.1 * esymm σ R a.1 * psum σ R a.2 :=
  psum_eq_mul_esymm_sub_sum (σ := σ) (R := R) n hn

-- ============================================================
-- Corollary 1: p₁ = e₁
-- ============================================================

/-- **Newton-Girard k=1**: The first power sum equals the first elementary symmetric polynomial:
      p₁ = e₁ -/
theorem psum_one_eq_esymm_one :
    psum σ R 1 = esymm σ R 1 := by
  rw [psum_one, esymm_one]

-- ============================================================
-- Corollary 2: p₂ = e₁² − 2·e₂
-- ============================================================

/-- **Newton-Girard k=2**: The second power sum satisfies:
      p₂ = e₁² − 2·e₂
    Equivalently: Σ xᵢ² = (Σ xᵢ)² − 2·Σ_{i<j} xᵢxⱼ. -/
theorem psum_two_eq :
    psum σ R 2 = esymm σ R 1 ^ 2 - 2 * esymm σ R 2 := by
  have h := psum_eq_mul_esymm_sub_sum (σ := σ) (R := R) 2 two_pos
  have hfilt : (antidiagonal 2).filter (fun a => a.1 ∈ Set.Ioo 0 2) = {(1, 1)} := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_antidiagonal, Set.mem_Ioo, mem_singleton, Prod.mk.injEq]
    omega
  rw [hfilt, sum_singleton] at h
  rw [h, psum_one_eq_esymm_one]
  ring

-- ============================================================
-- Corollary 3: p₃ = e₁·p₂ − e₂·p₁ + 3·e₃
-- ============================================================

/-- **Newton-Girard k=3**: The third power sum satisfies:
      p₃ = e₁·p₂ − e₂·p₁ + 3·e₃ -/
theorem psum_three_eq :
    psum σ R 3 =
      esymm σ R 1 * psum σ R 2 - esymm σ R 2 * psum σ R 1 + 3 * esymm σ R 3 := by
  have h := psum_eq_mul_esymm_sub_sum (σ := σ) (R := R) 3 (by norm_num)
  have hfilt : (antidiagonal 3).filter (fun a => a.1 ∈ Set.Ioo 0 3) =
      {(1, 2), (2, 1)} := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_antidiagonal, Set.mem_Ioo, mem_insert, mem_singleton,
               Prod.mk.injEq]
    omega
  rw [hfilt, sum_insert (by decide : (1, 2) ∉ ({(2, 1)} : Finset (ℕ × ℕ))),
      sum_singleton] at h
  rw [h]
  ring

end AMGMInequalityOQ02OQ01OQ02OQ01
