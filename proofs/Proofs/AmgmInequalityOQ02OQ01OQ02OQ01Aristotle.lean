/-
  Aristotle targets for amgm-inequality-oq-02-oq-01-oq-02-oq-01
  Newton-Girard corollaries k=1,2,3.
  See AmgmInequalityOQ02OQ01OQ02OQ01.lean for the main formalization.

  All 3 targets now proved via MvPolynomial.psum_eq_mul_esymm_sub_sum
  with antidiagonal filter evaluation and linear_combination.
-/
import Mathlib

open MvPolynomial Finset BigOperators Set

namespace AmgmInequalityOQ02OQ01OQ02OQ01Aristotle

variable (σ : Type*) (R : Type*) [CommRing R] [Fintype σ]

private lemma antidiag_filter_one :
    (antidiagonal 1).filter (fun a => a.1 ∈ Ioo 0 1) = ∅ := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_antidiagonal, mem_Ioo, Finset.notMem_empty, iff_false, not_and]
  omega

private lemma antidiag_filter_two :
    (antidiagonal 2).filter (fun a => a.1 ∈ Ioo 0 2) = {(1, 1)} := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_antidiagonal, mem_Ioo, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hab, ha_pos, ha_lt⟩; omega
  · rintro ⟨rfl, rfl⟩; omega

private lemma antidiag_filter_three :
    (antidiagonal 3).filter (fun a => a.1 ∈ Ioo 0 3) = {(1, 2), (2, 1)} := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_antidiagonal, mem_Ioo, mem_insert, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hab, ha_pos, ha_lt⟩; omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega

theorem psum_one_eq_esymm_one :
    psum σ R 1 = esymm σ R 1 := by
  have h := MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 1 (by omega)
  rw [antidiag_filter_one, sum_empty, sub_zero] at h
  linear_combination h

theorem psum_two_eq :
    psum σ R 2 = esymm σ R 1 ^ 2 - 2 * esymm σ R 2 := by
  have h₁ := psum_one_eq_esymm_one σ R
  have h := MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 2 (by omega)
  rw [antidiag_filter_two, sum_singleton] at h
  linear_combination h + esymm σ R 1 * h₁

theorem psum_three_eq :
    psum σ R 3 =
      esymm σ R 1 * psum σ R 2 - esymm σ R 2 * psum σ R 1 + 3 * esymm σ R 3 := by
  have h := MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 3 (by omega)
  rw [antidiag_filter_three] at h
  rw [sum_insert (show (1, 2) ∉ ({(2, 1)} : Finset _) by decide), sum_singleton] at h
  linear_combination h

end AmgmInequalityOQ02OQ01OQ02OQ01Aristotle
