/-
  Full Newton-Girard Recurrence for Symmetric Polynomials

  Open Question (amgm-inequality-oq-02-oq-01-oq-02-oq-01):
  Prove the general Newton-Girard recurrence connecting power sums
    pₖ = Σ xᵢᵏ
  and elementary symmetric polynomials
    eₖ = Σ_{i₁<...<iₖ} xᵢ₁...xᵢₖ
  for all k ≥ 1.

  Mathlib provides MvPolynomial.psum_eq_mul_esymm_sub_sum which states:
    pₙ = (-1)^(n+1) · n · eₙ − Σ_{a ∈ antidiag n, 0<a.1<n} (-1)^a.1 · e_{a.1} · p_{a.2}

  Corollaries (k = 1, 2, 3):
    p₁ = e₁
    p₂ = e₁² − 2·e₂
    p₃ = e₁·p₂ − e₂·p₁ + 3·e₃

  Status: PROVED — all three corollaries derived from psum_eq_mul_esymm_sub_sum.
  Axioms: 0, Sorries: 0
  Tags: algebra, symmetric-functions, newton-girard, power-sums, mv-polynomial
-/

import Mathlib

namespace AMGMInequalityOQ02OQ01OQ02OQ01

open MvPolynomial Finset BigOperators Set

variable (σ : Type*) (R : Type*) [CommRing R] [Fintype σ]

-- ============================================================
-- Corollary 1: p₁ = e₁
-- ============================================================

/-- **Newton-Girard k=1**: The first power sum equals the first elementary symmetric polynomial:
      p₁ = e₁
    Proof: both equal ∑ i : σ, X i (from Mathlib's psum_one and esymm_one). -/
theorem psum_one_eq_esymm_one :
    psum σ R 1 = esymm σ R 1 :=
  (MvPolynomial.psum_one σ R).trans (MvPolynomial.esymm_one σ R).symm

-- ============================================================
-- Corollary 2: p₂ = e₁² − 2·e₂
-- ============================================================

/-- **Newton-Girard k=2**: The second power sum satisfies:
      p₂ = e₁² − 2·e₂
    Equivalently: Σ xᵢ² = (Σ xᵢ)² − 2·Σ_{i<j} xᵢxⱼ.

    Proof: Apply psum_eq_mul_esymm_sub_sum at k=2. The antidiagonal {a : a.1+a.2=2, 0<a.1<2}
    = {(1,1)}, so psum 2 = (-1)³·2·e₂ − (-1)¹·e₁·p₁ = -2e₂ + e₁² = e₁² - 2e₂. -/
theorem psum_two_eq :
    psum σ R 2 = esymm σ R 1 ^ 2 - 2 * esymm σ R 2 := by
  have h1 : psum σ R 1 = esymm σ R 1 := psum_one_eq_esymm_one σ R
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 2 two_pos]
  have hfilt : (Finset.antidiagonal 2).filter (fun a : ℕ × ℕ => a.1 ∈ Ioo 0 2) =
               {(1, 1)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonal, mem_Ioo,
               Finset.mem_singleton, Prod.mk.injEq]
    omega
  simp only [hfilt, Finset.sum_singleton, h1]
  ring

-- ============================================================
-- Corollary 3: p₃ = e₁·p₂ − e₂·p₁ + 3·e₃
-- ============================================================

/-- **Newton-Girard k=3**: The third power sum satisfies:
      p₃ = e₁·p₂ − e₂·p₁ + 3·e₃

    Proof: Apply psum_eq_mul_esymm_sub_sum at k=3. The antidiagonal {a : a.1+a.2=3, 0<a.1<3}
    = {(1,2), (2,1)}, so:
    psum 3 = (-1)⁴·3·e₃ − ((-1)¹·e₁·p₂ + (-1)²·e₂·p₁)
           = 3e₃ + e₁·p₂ − e₂·p₁ = e₁·p₂ − e₂·p₁ + 3e₃. -/
theorem psum_three_eq :
    psum σ R 3 =
      esymm σ R 1 * psum σ R 2 - esymm σ R 2 * psum σ R 1 + 3 * esymm σ R 3 := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 3 (by norm_num)]
  have hfilt : (Finset.antidiagonal 3).filter (fun a : ℕ × ℕ => a.1 ∈ Ioo 0 3) =
               {(1, 2), (2, 1)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonal, mem_Ioo,
               Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  simp only [hfilt, Finset.sum_insert (by decide : (1, 2) ∉ ({(2, 1)} : Finset (ℕ × ℕ))),
             Finset.sum_singleton]
  ring

end AMGMInequalityOQ02OQ01OQ02OQ01
