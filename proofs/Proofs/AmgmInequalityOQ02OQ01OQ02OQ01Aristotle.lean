/-
  Aristotle targets for amgm-inequality-oq-02-oq-01-oq-02-oq-01
  Newton-Girard corollaries k=1,2,3 for automated proof search.
  See AmgmInequalityOQ02OQ01OQ02OQ01.lean for the main formalization.

  The 3 sorries in the main file are Newton-Girard corollaries for
  MvPolynomial power sums and elementary symmetric polynomials.

  ## Proof Strategies

  TARGET 1 (psum_one_eq_esymm_one):
    Apply psum_eq_mul_esymm_sub_sum at n=1:
      psum σ R 1 = (-1)^2 * 1 * esymm σ R 1 - (empty sum over antidiag 1 filtered by 0<a<1)
      = 1 * esymm σ R 1 - 0 = esymm σ R 1
    The sum is empty because no a satisfies 0 < a < 1 for natural numbers.
    Strategy: have h := MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 1 one_ne_zero
              simp [Finset.antidiagonal, Set.Ioo] at h; linarith

  TARGET 2 (psum_two_eq):
    Apply psum_eq_mul_esymm_sub_sum at n=2.
    antidiag(2) filtered by 0<a<2 = {(1,1)}, so:
      psum σ R 2 = (-1)^3 * 2 * esymm σ R 2 - (-1)^1 * esymm σ R 1 * psum σ R 1
               = -2*esymm 2 + esymm 1 * psum 1
               = -2*esymm 2 + esymm 1 * esymm 1   (using psum 1 = esymm 1)
               = esymm 1 ^ 2 - 2 * esymm 2
    Strategy: rw [psum_one_eq_esymm_one]
              have h := MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 2 (by norm_num)
              simp [Finset.antidiagonal, Set.Ioo] at h
              ring_nf at h ⊢; exact h

  TARGET 3 (psum_three_eq):
    Apply psum_eq_mul_esymm_sub_sum at n=3.
    antidiag(3) filtered by 0<a<3 = {(1,2), (2,1)}, so:
      psum σ R 3 = (-1)^4 * 3 * esymm σ R 3
                - (-1)^1 * esymm σ R 1 * psum σ R 2
                - (-1)^2 * esymm σ R 2 * psum σ R 1
               = 3*esymm 3 + esymm 1 * psum 2 - esymm 2 * psum 1
    Strategy: rw [psum_one_eq_esymm_one]
              have h := MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 3 (by norm_num)
              simp [Finset.antidiagonal, Set.Ioo] at h
              ring_nf at h ⊢; exact h
-/
import Mathlib

open MvPolynomial Finset BigOperators Set

namespace AmgmInequalityOQ02OQ01OQ02OQ01Aristotle

variable (σ : Type*) (R : Type*) [CommRing R] [Fintype σ]

/-
TARGET 1: Newton-Girard k=1 — the first power sum equals the first
elementary symmetric polynomial.

psum σ R 1 = Σ_{i : σ} X i = esymm σ R 1
-/
theorem psum_one_eq_esymm_one :
    psum σ R 1 = esymm σ R 1 := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 1 one_ne_zero]
  have hfilt : (Finset.antidiagonal 1).filter (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 1) = ∅ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo,
               Finset.not_mem_empty, iff_false, not_and, not_lt]
    omega
  simp only [hfilt, Finset.sum_empty]
  ring

/-
TARGET 2: Newton-Girard k=2 — power sum in terms of elementary symmetric polynomials.

p₂ = e₁² − 2·e₂

Derivation via psum_eq_mul_esymm_sub_sum at n=2:
  antidiag(2) ∩ {0<a<2} = {(1,1)}, so the sum has one term:
  psum 2 = -2·esymm 2 - (-1)·esymm 1·psum 1 = e₁² - 2·e₂
-/
theorem psum_two_eq :
    psum σ R 2 = esymm σ R 1 ^ 2 - 2 * esymm σ R 2 := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 2 (by norm_num)]
  have hfilt : (Finset.antidiagonal 2).filter (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 2) =
               {(1, 1)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo,
               Finset.mem_singleton, Prod.mk.injEq]
    omega
  simp only [hfilt, Finset.sum_singleton]
  rw [psum_one_eq_esymm_one]
  ring

/-
TARGET 3: Newton-Girard k=3 — power sum in terms of lower-degree power sums.

p₃ = e₁·p₂ − e₂·p₁ + 3·e₃

Derivation via psum_eq_mul_esymm_sub_sum at n=3:
  antidiag(3) ∩ {0<a<3} = {(1,2), (2,1)}, so the sum has two terms:
  psum 3 = 3·esymm 3 - (-1)·esymm 1·psum 2 - 1·esymm 2·psum 1
         = 3·e₃ + e₁·p₂ - e₂·p₁
         = e₁·p₂ - e₂·p₁ + 3·e₃
-/
theorem psum_three_eq :
    psum σ R 3 =
      esymm σ R 1 * psum σ R 2 - esymm σ R 2 * psum σ R 1 + 3 * esymm σ R 3 := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 3 (by norm_num)]
  have hfilt : (Finset.antidiagonal 3).filter (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 3) =
               {(1, 2), (2, 1)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo,
               Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  simp only [hfilt,
             Finset.sum_insert (by decide : (1, 2) ∉ ({(2, 1)} : Finset (ℕ × ℕ))),
             Finset.sum_singleton]
  rw [psum_one_eq_esymm_one]
  ring

end AmgmInequalityOQ02OQ01OQ02OQ01Aristotle
