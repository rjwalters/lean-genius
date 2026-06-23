/-
  Newton-Girard Recurrence: k=4 and k=5 Extensions
  Open Question (amgm-inequality-oq-02-oq-01-oq-02-oq-01-oq-01):
  Extend the k=1,2,3 Newton-Girard corollaries to k=4 and k=5.

  Parent proof (AmgmInequalityOQ02OQ01OQ02OQ01.lean) established:
    p₁ = e₁
    p₂ = e₁² − 2·e₂
    p₃ = e₁·p₂ − e₂·p₁ + 3·e₃

  This file extends to:
    k=4: p₄ = e₁·p₃ − e₂·p₂ + e₃·p₁ − 4·e₄
    k=5: p₅ = e₁·p₄ − e₂·p₃ + e₃·p₂ − e₄·p₁ + 5·e₅

  Both follow from Mathlib's MvPolynomial.psum_eq_mul_esymm_sub_sum:
    pₙ = (-1)^(n+1)·n·eₙ − ∑_{0<a<n} (-1)^a · eₐ · pₙ₋ₐ

  The antidiagonals:
    k=4: {(a,b) | a+b=4, 0<a<4} = {(1,3),(2,2),(3,1)}
    k=5: {(a,b) | a+b=5, 0<a<5} = {(1,4),(2,3),(3,2),(4,1)}

  Dual expressions (eₖ in terms of power sums):
    4·e₄ = e₃·p₁ − e₂·p₂ + e₁·p₃ − p₄
    5·e₅ = e₄·p₁ − e₃·p₂ + e₂·p₃ − e₁·p₄ + p₅

  Status: PROVED — k=4 and k=5 via antidiagonal template + ring
  Axioms: 0, Sorries: 0
  Tags: algebra, symmetric-functions, newton-girard, power-sums, mv-polynomial
-/

import Mathlib

namespace AmgmInequalityOQ02OQ01OQ02OQ01OQ01

open MvPolynomial Finset BigOperators Set

variable (σ : Type*) (R : Type*) [CommRing R] [Fintype σ]

-- ============================================================
-- Corollary 4: p₄ = e₁·p₃ − e₂·p₂ + e₃·p₁ − 4·e₄
-- ============================================================

/-- **Newton-Girard k=4**: The fourth power sum satisfies:
      p₄ = e₁·p₃ − e₂·p₂ + e₃·p₁ − 4·e₄

    Proof: Apply `psum_eq_mul_esymm_sub_sum` at k=4.
    The antidiagonal {(a,b) | a+b=4, 0<a<4} = {(1,3),(2,2),(3,1)}.
    This gives:
      p₄ = (-1)⁵·4·e₄ − ((-1)¹·e₁·p₃ + (-1)²·e₂·p₂ + (-1)³·e₃·p₁)
         = −4e₄ + e₁p₃ − e₂p₂ + e₃p₁
    Closed by ring. -/
theorem psum_four_eq :
    psum σ R 4 = esymm σ R 1 * psum σ R 3 - esymm σ R 2 * psum σ R 2 +
                esymm σ R 3 * psum σ R 1 - 4 * esymm σ R 4 := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 4 (by norm_num)]
  have hfilt : (Finset.antidiagonal 4).filter (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 4) =
               {(1, 3), (2, 2), (3, 1)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo,
               Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  simp only [hfilt,
             Finset.sum_insert (by decide : (1, 3) ∉ ({(2, 2), (3, 1)} : Finset (ℕ × ℕ))),
             Finset.sum_insert (by decide : (2, 2) ∉ ({(3, 1)} : Finset (ℕ × ℕ))),
             Finset.sum_singleton]
  ring

-- ============================================================
-- Corollary 5: p₅ = e₁·p₄ − e₂·p₃ + e₃·p₂ − e₄·p₁ + 5·e₅
-- ============================================================

/-- **Newton-Girard k=5**: The fifth power sum satisfies:
      p₅ = e₁·p₄ − e₂·p₃ + e₃·p₂ − e₄·p₁ + 5·e₅

    Proof: Apply `psum_eq_mul_esymm_sub_sum` at k=5.
    The antidiagonal {(a,b) | a+b=5, 0<a<5} = {(1,4),(2,3),(3,2),(4,1)}.
    This gives:
      p₅ = (-1)⁶·5·e₅ − ((-1)¹·e₁·p₄ + (-1)²·e₂·p₃ + (-1)³·e₃·p₂ + (-1)⁴·e₄·p₁)
         = 5e₅ + e₁p₄ − e₂p₃ + e₃p₂ − e₄p₁
    Closed by ring. -/
theorem psum_five_eq :
    psum σ R 5 = esymm σ R 1 * psum σ R 4 - esymm σ R 2 * psum σ R 3 +
                esymm σ R 3 * psum σ R 2 - esymm σ R 4 * psum σ R 1 +
                5 * esymm σ R 5 := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 5 (by norm_num)]
  have hfilt : (Finset.antidiagonal 5).filter (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 5) =
               {(1, 4), (2, 3), (3, 2), (4, 1)} := by
    ext ⟨a, b⟩
    constructor
    · intro h
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo] at h
      obtain ⟨hab, ha_pos, ha_lt⟩ := h
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      omega
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo]
      omega
  simp only [hfilt,
             Finset.sum_insert (by decide : (1, 4) ∉ ({(2, 3), (3, 2), (4, 1)} : Finset (ℕ × ℕ))),
             Finset.sum_insert (by decide : (2, 3) ∉ ({(3, 2), (4, 1)} : Finset (ℕ × ℕ))),
             Finset.sum_insert (by decide : (3, 2) ∉ ({(4, 1)} : Finset (ℕ × ℕ))),
             Finset.sum_singleton]
  ring

-- ============================================================
-- Dual forms: expressing eₖ in terms of power sums
-- ============================================================

/-- **Newton-Girard dual k=4**: The fourth elementary symmetric polynomial
    expressed via power sums:
      4·e₄ = e₃·p₁ − e₂·p₂ + e₁·p₃ − p₄

    This is the dual form of Newton-Girard k=4, obtained by rearranging
    psum_four_eq. Works over any CommRing. -/
theorem esymm_four_from_psum :
    4 * esymm σ R 4 = esymm σ R 3 * psum σ R 1 - esymm σ R 2 * psum σ R 2 +
                     esymm σ R 1 * psum σ R 3 - psum σ R 4 := by
  linear_combination psum_four_eq σ R

/-- **Newton-Girard dual k=5**: The fifth elementary symmetric polynomial
    expressed via power sums:
      5·e₅ = e₄·p₁ − e₃·p₂ + e₂·p₃ − e₁·p₄ + p₅

    This is the dual form of Newton-Girard k=5, obtained by rearranging
    psum_five_eq. Works over any CommRing. -/
theorem esymm_five_from_psum :
    5 * esymm σ R 5 = esymm σ R 4 * psum σ R 1 - esymm σ R 3 * psum σ R 2 +
                     esymm σ R 2 * psum σ R 3 - esymm σ R 1 * psum σ R 4 +
                     psum σ R 5 := by
  linear_combination -(psum_five_eq σ R)

end AmgmInequalityOQ02OQ01OQ02OQ01OQ01
