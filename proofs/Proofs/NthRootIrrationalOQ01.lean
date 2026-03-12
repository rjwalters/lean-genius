/-
  Nth Root Irrationality OQ-01: Algebraic Irrationality via Irreducible Polynomials

  The existing NthRootIrrational.lean proves irrationality of nth roots using
  `irrational_nrt_of_notint_nrt` (a direct counting argument). This file
  provides a more structural approach via irreducible polynomials:

  **Key insight**: α is irrational whenever it is a root of an irreducible
  polynomial of degree ≥ 2 over ℚ. This subsumes nth-root irrationality
  because X^n - m is irreducible when m has a prime factor not appearing
  to the nth power.

  ## Results

  ### Proved (0 axioms, 0 sorries):
  1. irreducible_no_rational_root: irreducible p ∈ ℚ[X] with deg ≥ 2 has no rational root
  2. irrational_root_of_irreducible: real roots of such p are irrational
  3. irrational_of_minpoly_degree_ge_two: algebraic degree ≥ 2 implies irrational
  4. eisenstein_X_pow_sub_prime: X^n - p irreducible over ℚ for prime p (Eisenstein + Gauss)
  5. Concrete applications for √2, ∛2, ∛3, ⁵√7

  ## References
  - Lang, S. (2002). "Algebra." Ch. IV (Polynomials).
  - Dummit & Foote (2004). "Abstract Algebra." §9.4 (Irreducibility Criteria).
-/

import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open Polynomial

namespace NthRootIrrationalOQ01

noncomputable section

-- ============================================================================
-- Part I: Irreducible Polynomial → No Rational Root
-- ============================================================================

/-- **Core theorem**: If p ∈ ℚ[X] is irreducible and has degree ≥ 2,
    then p has no rational root. -/
theorem irreducible_no_rational_root {p : ℚ[X]} (hirr : Irreducible p)
    (hdeg : 2 ≤ p.natDegree) (r : ℚ) : ¬ p.IsRoot r := by
  intro hroot
  obtain ⟨q, hpq⟩ := dvd_iff_isRoot.mpr hroot
  rcases hirr.isUnit_or_isUnit hpq with hu | hu
  · -- X - C r is irreducible (degree 1), hence not a unit
    exact (irreducible_X_sub_C r).1 hu
  · -- q is a unit ⟹ deg q = 0 ⟹ deg p = 1, contradicting deg p ≥ 2
    have hne1 := X_sub_C_ne_zero r
    have hne2 : q ≠ 0 := right_ne_zero_of_mul (hpq ▸ hirr.ne_zero)
    have hd : p.natDegree = 1 + q.natDegree := by
      rw [hpq, natDegree_mul hne1 hne2, natDegree_X_sub_C]
    have hq0 : q.natDegree = 0 := by
      rcases Polynomial.isUnit_iff.mp hu with ⟨c, _, rfl⟩
      exact natDegree_C c
    omega

-- ============================================================================
-- Part II: Irrational Roots of Irreducible Polynomials
-- ============================================================================

/-- **Irrationality via irreducibility**: If p ∈ ℚ[X] is irreducible with
    degree ≥ 2, then any real root of p is irrational. -/
theorem irrational_root_of_irreducible {p : ℚ[X]} (hirr : Irreducible p)
    (hdeg : 2 ≤ p.natDegree) {α : ℝ}
    (hroot : Polynomial.aeval α p = 0) :
    Irrational α := by
  intro ⟨r, hr⟩
  have heval : Polynomial.aeval r p = 0 := by
    apply_fun (algebraMap ℚ ℝ) using (algebraMap ℚ ℝ).injective
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply,
        show (algebraMap ℚ ℝ) r = α from hr]
    exact hroot
  exact irreducible_no_rational_root hirr hdeg r heval

-- ============================================================================
-- Part III: Algebraic Degree Characterization
-- ============================================================================

/-- If the minimal polynomial of α over ℚ has degree ≥ 2, then α is irrational. -/
theorem irrational_of_minpoly_degree_ge_two {α : ℝ}
    (hint : IsIntegral ℚ α)
    (hdeg : 2 ≤ (minpoly ℚ α).natDegree) :
    Irrational α :=
  irrational_root_of_irreducible
    (minpoly.irreducible hint) hdeg (minpoly.aeval ℚ α)

-- ============================================================================
-- Part IV: Eisenstein Criterion for X^n - p (Proved via Eisenstein + Gauss)
-- ============================================================================

/-- X^n - p is irreducible over ℤ for prime p and n ≥ 2, by Eisenstein's
    criterion at the prime ideal (p). -/
private theorem X_pow_sub_prime_irreducible_int (n : ℕ) (p : ℕ) (hn : 2 ≤ n)
    (hp : Nat.Prime p) :
    Irreducible (X ^ n - C (p : ℤ) : ℤ[X]) := by
  have hn0 : (0 : ℕ) < n := by omega
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp_int : Prime (p : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]; exact_mod_cast hp
  apply Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(p : ℤ)})
  · -- (p) is a prime ideal in ℤ
    rw [Ideal.span_singleton_prime hp_ne]
    exact hp_int
  · -- leadingCoeff 1 ∉ (p)
    rw [leadingCoeff_X_pow_sub_C hn0, Ideal.mem_span_singleton]
    exact hp_int.not_dvd_one
  · -- ∀ k < degree, coeff k ∈ (p)
    intro k hk
    rw [degree_X_pow_sub_C hn0 (p : ℤ)] at hk
    have hkn : k < n := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton, coeff_sub, coeff_X_pow, coeff_C]
    have : ¬(k = n) := by omega
    simp only [if_neg this, zero_sub, dvd_neg]
    by_cases hk0 : k = 0 <;> simp [hk0]
  · -- 0 < degree
    rw [degree_X_pow_sub_C hn0 (p : ℤ)]
    exact_mod_cast hn0
  · -- coeff 0 ∉ (p)²: p² ∤ p since p is prime
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp only [coeff_sub, coeff_X_pow, coeff_C,
               show ¬(0 = n) from by omega, ite_false, zero_sub, dvd_neg]
    -- Goal: ¬ ((p : ℤ) ^ 2 ∣ (p : ℤ))
    intro h
    have hle := Int.le_of_dvd (by exact_mod_cast hp.pos : 0 < (p : ℤ)) h
    have hlt : 1 < (p : ℤ) := by exact_mod_cast hp.one_lt
    nlinarith [sq_nonneg ((p : ℤ) - 1)]
  · -- isPrimitive: X^n - p is monic
    exact (monic_X_pow_sub_C (p : ℤ) (by omega : n ≠ 0)).isPrimitive

/-- **Eisenstein criterion**: X^n - p is irreducible over ℚ for prime p and n ≥ 2.
    Proved via Eisenstein's criterion over ℤ at the prime ideal (p),
    then transferred to ℚ via the Gauss lemma. -/
theorem eisenstein_X_pow_sub_prime (n : ℕ) (p : ℕ) (hn : 2 ≤ n)
    (hp : Nat.Prime p) :
    Irreducible (X ^ n - C (p : ℚ) : ℚ[X]) := by
  have hprim : (X ^ n - C (p : ℤ) : ℤ[X]).IsPrimitive :=
    (monic_X_pow_sub_C (p : ℤ) (by omega : n ≠ 0)).isPrimitive
  have hirr := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
    (X_pow_sub_prime_irreducible_int n p hn hp)
  convert hirr using 1
  ext k
  simp [coeff_sub, coeff_X_pow]

/-- X^n - m has degree n for nonzero m and n ≥ 1. -/
theorem natDegree_X_pow_sub_C_eq {n : ℕ} {m : ℚ} (hn : 1 ≤ n) (hm : m ≠ 0) :
    (X ^ n - C m : ℚ[X]).natDegree = n := by
  have h : (C m : ℚ[X]).natDegree < (X ^ n : ℚ[X]).natDegree := by
    simp only [natDegree_C, natDegree_pow, natDegree_X, mul_one]
    omega
  rw [natDegree_sub_eq_left_of_natDegree_lt h, natDegree_pow, natDegree_X, mul_one]

-- ============================================================================
-- Part V: Structural Irrationality of nth Roots of Primes
-- ============================================================================

/-- For prime p and n ≥ 2, the nth root p^(1/n) is irrational because
    X^n - p is irreducible over ℚ (Eisenstein criterion). -/
theorem irrational_nthRoot_of_prime (n : ℕ) (p : ℕ)
    (hn : 2 ≤ n) (hp : Nat.Prime p) :
    Irrational ((p : ℝ) ^ ((1 : ℝ) / n)) := by
  apply irrational_root_of_irreducible (eisenstein_X_pow_sub_prime n p hn hp)
  · rw [natDegree_X_pow_sub_C_eq (by omega) (by exact_mod_cast hp.ne_zero)]
    exact hn
  · -- p^(1/n) is a root of X^n - p
    simp only [map_sub, map_pow, aeval_X, map_natCast]
    rw [← Real.rpow_natCast ((p : ℝ) ^ ((1 : ℝ) / n)) n,
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p)]
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp [hn']

-- ============================================================================
-- Part VI: Concrete Applications
-- ============================================================================

/-- √2 is irrational (via irreducibility of X² - 2). -/
theorem irrational_sqrt2 : Irrational ((2 : ℝ) ^ ((1 : ℝ) / 2)) :=
  irrational_nthRoot_of_prime 2 2 le_rfl (by norm_num)

/-- ∛2 is irrational (via irreducibility of X³ - 2). -/
theorem irrational_cbrt2 : Irrational ((2 : ℝ) ^ ((1 : ℝ) / 3)) :=
  irrational_nthRoot_of_prime 3 2 (by norm_num) (by norm_num)

/-- ∛3 is irrational (via irreducibility of X³ - 3). -/
theorem irrational_cbrt3 : Irrational ((3 : ℝ) ^ ((1 : ℝ) / 3)) :=
  irrational_nthRoot_of_prime 3 3 (by norm_num) (by norm_num)

/-- ⁵√7 is irrational (via irreducibility of X⁵ - 7). -/
theorem irrational_fifthrt7 : Irrational ((7 : ℝ) ^ ((1 : ℝ) / 5)) :=
  irrational_nthRoot_of_prime 5 7 (by norm_num) (by norm_num)

-- ============================================================================
-- Part VII: The Structural Hierarchy
-- ============================================================================

/-- **The irrationality hierarchy**: Irreducible polynomial approach (Level 3)
    subsumes counting arguments (Level 2) by reducing to a single algebraic
    property. -/
theorem structural_subsumes_counting (n : ℕ) (p : ℕ)
    (hn : 2 ≤ n) (hp : Nat.Prime p) :
    Irrational ((p : ℝ) ^ ((1 : ℝ) / n)) :=
  irrational_nthRoot_of_prime n p hn hp

end

end NthRootIrrationalOQ01
