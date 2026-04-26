/-
  Full Newton-Girard Recurrence for Symmetric Polynomials

  Open Question (amgm-inequality-oq-02-oq-01-oq-02-oq-01):
  Prove the general Newton-Girard recurrence connecting power sums
    pk = Sigma x_i^k
  and elementary symmetric polynomials
    ek = Sigma_{i1<...<ik} x_{i1}...x_{ik}
  for all k >= 1.

  Mathlib provides MvPolynomial.psum_eq_mul_esymm_sub_sum which states:
    pn = (-1)^(n+1) * n * en - Sigma_{0<i<n} (-1)^i * e_i * p_{n-i}

  Corollaries (k = 1, 2, 3):
    p1 = e1
    p2 = e1^2 - 2*e2
    p3 = e1*p2 - e2*p1 + 3*e3

  Status: Verified -- all corollaries proved via Mathlib's Newton identities.
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
    For n >= 1, the power sum pn satisfies:
      pn = (-1)^(n+1) * n * en - Sigma_{0<a<n} (-1)^a * e_a * p_{n-a}

    This is `MvPolynomial.psum_eq_mul_esymm_sub_sum` from Mathlib. -/
theorem newton_girard_recurrence (n : ℕ) (hn : 0 < n) :
    psum σ R n = (-1) ^ (n + 1) * (n : MvPolynomial σ R) * esymm σ R n -
      ∑ a ∈ antidiagonal n with a.1 ∈ Set.Ioo 0 n,
        (-1) ^ a.fst * esymm σ R a.1 * psum σ R a.2 :=
  MvPolynomial.psum_eq_mul_esymm_sub_sum σ R n hn

-- ============================================================
-- Helper: antidiagonal filter evaluations
-- ============================================================

/-- For k=1, there is no natural number strictly between 0 and 1,
    so the antidiagonal filter is empty. -/
private lemma antidiag_filter_one :
    (antidiagonal 1).filter (fun a => a.1 ∈ Set.Ioo 0 1) = ∅ := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_antidiagonal, Set.mem_Ioo, Finset.notMem_empty, iff_false, not_and]
  omega

/-- For k=2, the only pair (a,b) with a+b=2 and 0 < a < 2 is (1,1). -/
private lemma antidiag_filter_two :
    (antidiagonal 2).filter (fun a => a.1 ∈ Set.Ioo 0 2) = {(1, 1)} := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_antidiagonal, Set.mem_Ioo, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hab, ha_pos, ha_lt⟩; omega
  · rintro ⟨rfl, rfl⟩; omega

/-- For k=3, the pairs (a,b) with a+b=3 and 0 < a < 3 are (1,2) and (2,1). -/
private lemma antidiag_filter_three :
    (antidiagonal 3).filter (fun a => a.1 ∈ Set.Ioo 0 3) = {(1, 2), (2, 1)} := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_antidiagonal, Set.mem_Ioo, mem_insert, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hab, ha_pos, ha_lt⟩; omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega

-- ============================================================
-- Corollary 1: p1 = e1
-- ============================================================

/-- **Newton-Girard k=1**: The first power sum equals the first elementary symmetric polynomial:
      p1 = e1 -/
theorem psum_one_eq_esymm_one :
    psum σ R 1 = esymm σ R 1 := by
  have h := MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 1 (by omega)
  rw [antidiag_filter_one, sum_empty, sub_zero] at h
  linear_combination h

-- ============================================================
-- Corollary 2: p2 = e1^2 - 2*e2
-- ============================================================

/-- **Newton-Girard k=2**: The second power sum satisfies:
      p2 = e1^2 - 2*e2
    Equivalently: Sigma x_i^2 = (Sigma x_i)^2 - 2*Sigma_{i<j} x_i*x_j. -/
theorem psum_two_eq :
    psum σ R 2 = esymm σ R 1 ^ 2 - 2 * esymm σ R 2 := by
  have h₁ := psum_one_eq_esymm_one σ R
  have h := MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 2 (by omega)
  rw [antidiag_filter_two, sum_singleton] at h
  -- h : psum 2 = (-1)^3 * 2 * esymm 2 - (-1)^1 * esymm 1 * psum 1
  -- h1 : psum 1 = esymm 1
  -- Goal: psum 2 = esymm 1 ^ 2 - 2 * esymm 2
  linear_combination h + esymm σ R 1 * h₁

-- ============================================================
-- Corollary 3: p3 = e1*p2 - e2*p1 + 3*e3
-- ============================================================

/-- **Newton-Girard k=3**: The third power sum satisfies:
      p3 = e1*p2 - e2*p1 + 3*e3 -/
theorem psum_three_eq :
    psum σ R 3 =
      esymm σ R 1 * psum σ R 2 - esymm σ R 2 * psum σ R 1 + 3 * esymm σ R 3 := by
  have h := MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 3 (by omega)
  rw [antidiag_filter_three] at h
  rw [sum_insert (show (1, 2) ∉ ({(2, 1)} : Finset _) by decide), sum_singleton] at h
  -- h : psum 3 = (-1)^4 * 3 * esymm 3
  --     - ((-1)^1 * esymm 1 * psum 2 + (-1)^2 * esymm 2 * psum 1)
  -- = 3*e3 + e1*p2 - e2*p1
  linear_combination h

end AMGMInequalityOQ02OQ01OQ02OQ01
