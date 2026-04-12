import Mathlib

/-
# Algebraic Degree of n-th Roots: Non-Perfect-Power Criterion

**Open Question (from cube-root-2-irrational-oq-03)**:
Formalize the degree bound: any n-th root of a non-perfect-power is a
degree-n algebraic number.

## Mathematical Content

For a natural number m with a prime factor p satisfying p | m but p² ∤ m
(equivalently, m is not divisible by p² — a "square-free factor" condition),
and for any n ≥ 2:

1. X^n - m is irreducible over ℚ (Eisenstein criterion at p)
2. minpoly ℚ (m^(1/n)) = X^n - m
3. The algebraic degree [ℚ : ℚ(m^(1/n))] = n
4. [ℚ(m^(1/n)) : ℚ] = n (field extension degree equals n)

**Non-perfect-power connection**: If p | m but p² ∤ m and n ≥ 2, then m
cannot be a perfect n-th power (since any k^n would have v_p(k^n) = n·v_p(k),
which is either 0 or ≥ n > 1, never exactly 1).

## Examples Covered (beyond the prime case)

- ∛6 = 6^(1/3): p=2, 2|6, 4∤6 → degree 3
- ∛10 = 10^(1/3): p=2, 2|10, 4∤10 → degree 3
- ⁵√12 = 12^(1/5): p=3, 3|12, 9∤12 → degree 5
- ∜30: p=2, 2|30, 4∤30 → degree 4 (any square-free number)

## Status: 0 sorries, 0 axioms
-/

open Polynomial IntermediateField

set_option maxHeartbeats 800000

namespace CubeRoot2IrrationalOQ03

/-! ## Part I: Eisenstein Criterion for X^n - m with Square-Free Prime Factor -/

/-- X^n - m is irreducible over ℤ when m has a prime factor p with p | m but p² ∤ m.
    This follows from the Eisenstein criterion at the prime ideal (p). -/
private theorem eisenstein_X_pow_sub_int (n m p : ℕ) (hn : 2 ≤ n)
    (hp : Nat.Prime p) (hdvd : p ∣ m) (hndvd : ¬ p ^ 2 ∣ m) :
    Irreducible (X ^ n - C (m : ℤ) : ℤ[X]) := by
  have hn0 : (0 : ℕ) < n := by omega
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp_int : Prime (p : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]; exact_mod_cast hp
  apply Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(p : ℤ)})
  · -- (p) is a prime ideal in ℤ
    rw [Ideal.span_singleton_prime hp_ne]; exact hp_int
  · -- leading coefficient 1 ∉ (p)
    rw [leadingCoeff_X_pow_sub_C hn0, Ideal.mem_span_singleton]
    exact hp_int.not_dvd_one
  · -- ∀ k < degree, coeff k ∈ (p)
    intro k hk
    rw [degree_X_pow_sub_C hn0 (m : ℤ)] at hk
    have hkn : k < n := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton, coeff_sub, coeff_X_pow, coeff_C]
    have : ¬(k = n) := by omega
    simp only [if_neg this, zero_sub, dvd_neg]
    by_cases hk0 : k = 0
    · simp only [hk0, ite_true]
      exact_mod_cast hdvd
    · simp [hk0]
  · -- 0 < degree
    rw [degree_X_pow_sub_C hn0 (m : ℤ)]
    exact_mod_cast hn0
  · -- coeff 0 ∉ (p)²: p² ∤ m (by hypothesis)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp only [coeff_sub, coeff_X_pow, coeff_C,
               show ¬(0 = n) from by omega, ite_false, zero_sub, dvd_neg]
    intro h
    apply hndvd
    have : ((p ^ 2 : ℕ) : ℤ) ∣ (m : ℤ) := by push_cast; exact_mod_cast h
    exact_mod_cast this
  · -- IsPrimitive
    exact (monic_X_pow_sub_C (m : ℤ) (by omega : n ≠ 0)).isPrimitive

/-- X^n - m is irreducible over ℚ when m has a prime factor p with p | m but p² ∤ m.
    Proved via Eisenstein over ℤ, transferred to ℚ by the Gauss lemma. -/
theorem eisenstein_X_pow_sub_of_sqfree_factor (n m p : ℕ) (hn : 2 ≤ n)
    (hp : Nat.Prime p) (hdvd : p ∣ m) (hndvd : ¬ p ^ 2 ∣ m) (hm : m ≠ 0) :
    Irreducible (X ^ n - C (m : ℚ) : ℚ[X]) := by
  have hprim : (X ^ n - C (m : ℤ) : ℤ[X]).IsPrimitive :=
    (monic_X_pow_sub_C (m : ℤ) (by omega : n ≠ 0)).isPrimitive
  have hirr := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
    (eisenstein_X_pow_sub_int n m p hn hp hdvd hndvd)
  convert hirr using 1
  ext k
  simp [coeff_sub, coeff_X_pow]

/-! ## Part II: Root Identity and Integral Witness -/

/-- m^(1/n) is a root of X^n - m:
    aeval (m^(1/n)) (X^n - C(m:ℚ)) = (m^(1/n))^n - m = m - m = 0. -/
theorem aeval_nthRoot_sub_eq_zero (n m : ℕ) (hn : n ≠ 0) :
    Polynomial.aeval ((m : ℝ) ^ ((1 : ℝ) / n)) (X ^ n - C (m : ℚ) : ℚ[X]) = 0 := by
  simp only [map_sub, map_pow, aeval_X, map_natCast]
  rw [← Real.rpow_natCast ((m : ℝ) ^ ((1 : ℝ) / n)) n,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ m)]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp [hn']

/-- m^(1/n) is integral over ℚ: it satisfies the monic polynomial X^n - m ∈ ℚ[X]. -/
theorem isIntegral_nthRoot (n m : ℕ) (hn : n ≠ 0) :
    IsIntegral ℚ ((m : ℝ) ^ ((1 : ℝ) / n)) :=
  ⟨X ^ n - C (m : ℚ), monic_X_pow_sub_C _ hn, aeval_nthRoot_sub_eq_zero n m hn⟩

/-! ## Part III: Minimal Polynomial -/

/-- X^n - m has degree n for nonzero m and n ≥ 1. -/
theorem natDegree_X_pow_sub_nat_eq {n : ℕ} {m : ℕ} (hn : 1 ≤ n) (hm : m ≠ 0) :
    (X ^ n - C (m : ℚ) : ℚ[X]).natDegree = n := by
  have h : (C (m : ℚ) : ℚ[X]).natDegree < (X ^ n : ℚ[X]).natDegree := by
    simp only [natDegree_C, natDegree_pow, natDegree_X, mul_one]
    omega
  rw [natDegree_sub_eq_left_of_natDegree_lt h, natDegree_pow, natDegree_X, mul_one]

/-- The minimal polynomial of m^(1/n) over ℚ equals X^n - m,
    when m has a prime factor p with p | m but p² ∤ m. -/
theorem minpoly_nthRoot_eq (n m p : ℕ) (hn : 2 ≤ n)
    (hp : Nat.Prime p) (hdvd : p ∣ m) (hndvd : ¬ p ^ 2 ∣ m) (hm : 0 < m) :
    X ^ n - C (m : ℚ) = minpoly ℚ ((m : ℝ) ^ ((1 : ℝ) / n)) :=
  minpoly.eq_of_irreducible_of_monic
    (eisenstein_X_pow_sub_of_sqfree_factor n m p hn hp hdvd hndvd hm.ne')
    (aeval_nthRoot_sub_eq_zero n m (by omega))
    (monic_X_pow_sub_C (m : ℚ) (by omega : n ≠ 0))

/-! ## Part IV: Algebraic Degree Results -/

/-- **Main Result**: The algebraic degree of m^(1/n) over ℚ is exactly n,
    when m has a prime factor p with p | m but p² ∤ m.

    This formalizes the "degree bound" for n-th roots of non-perfect-powers:
    since p | m but p² ∤ m implies m is not a perfect n-th power (for n ≥ 2),
    the minimal polynomial X^n - m is irreducible, giving degree exactly n. -/
theorem minpoly_nthRoot_natDegree (n m p : ℕ) (hn : 2 ≤ n)
    (hp : Nat.Prime p) (hdvd : p ∣ m) (hndvd : ¬ p ^ 2 ∣ m) (hm : 0 < m) :
    (minpoly ℚ ((m : ℝ) ^ ((1 : ℝ) / n))).natDegree = n := by
  rw [← minpoly_nthRoot_eq n m p hn hp hdvd hndvd hm]
  exact natDegree_X_pow_sub_nat_eq (by omega) hm.ne'

/-- **Field Extension Degree**: [ℚ(m^(1/n)) : ℚ] = n,
    when m has a prime factor p with p | m but p² ∤ m. -/
theorem adjoin_nthRoot_finrank (n m p : ℕ) (hn : 2 ≤ n)
    (hp : Nat.Prime p) (hdvd : p ∣ m) (hndvd : ¬ p ^ 2 ∣ m) (hm : 0 < m) :
    Module.finrank ℚ ℚ⟮(m : ℝ) ^ ((1 : ℝ) / ↑n)⟯ = n := by
  rw [IntermediateField.adjoin.finrank (isIntegral_nthRoot n m (by omega))]
  exact minpoly_nthRoot_natDegree n m p hn hp hdvd hndvd hm

/-! ## Part V: Non-Perfect-Power Criterion -/

/-- A number m with a prime factor p satisfying p | m but p² ∤ m
    cannot be a perfect n-th power (for n ≥ 2).

    Proof: if m = k^n, then v_p(m) = n · v_p(k). But v_p(m) = 1
    (since p | m but p² ∤ m), so n · v_p(k) = 1. Since n ≥ 2,
    this forces v_p(k) = 0 and n = 1, contradiction. -/
theorem not_perfect_power_of_sqfree_factor (n m p : ℕ) (hn : 2 ≤ n)
    (hp : Nat.Prime p) (hdvd : p ∣ m) (hndvd : ¬ p ^ 2 ∣ m) :
    ¬ ∃ k : ℕ, m = k ^ n := by
  rintro ⟨k, rfl⟩
  apply hndvd
  -- p | k^n and p prime → p | k
  have hdvdk : p ∣ k := hp.dvd_of_dvd_pow hdvd
  -- p^2 | k^2 | k^n
  calc p ^ 2 ∣ k ^ 2 := pow_dvd_pow_of_dvd hdvdk 2
       _ ∣ k ^ n     := Nat.pow_dvd_pow k hn

/-! ## Part VI: Concrete Applications -/

/-- ∛6 has algebraic degree 3 over ℚ.
    (6 = 2·3; p=2, 2|6, 4∤6 → Eisenstein gives X³-6 irreducible) -/
theorem adjoin_cbrt6_finrank :
    Module.finrank ℚ ℚ⟮(6 : ℝ) ^ ((1 : ℝ) / 3)⟯ = 3 :=
  adjoin_nthRoot_finrank 3 6 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- ∛10 has algebraic degree 3 over ℚ.
    (10 = 2·5; p=2, 2|10, 4∤10 → Eisenstein gives X³-10 irreducible) -/
theorem adjoin_cbrt10_finrank :
    Module.finrank ℚ ℚ⟮(10 : ℝ) ^ ((1 : ℝ) / 3)⟯ = 3 :=
  adjoin_nthRoot_finrank 3 10 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- ⁵√12 has algebraic degree 5 over ℚ.
    (12 = 4·3; p=3, 3|12, 9∤12 → Eisenstein gives X⁵-12 irreducible) -/
theorem adjoin_fifthrt12_finrank :
    Module.finrank ℚ ℚ⟮(12 : ℝ) ^ ((1 : ℝ) / 5)⟯ = 5 :=
  adjoin_nthRoot_finrank 5 12 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- ∜30 has algebraic degree 4 over ℚ.
    (30 = 2·3·5; p=2, 2|30, 4∤30 → Eisenstein gives X⁴-30 irreducible) -/
theorem adjoin_fourthrt30_finrank :
    Module.finrank ℚ ℚ⟮(30 : ℝ) ^ ((1 : ℝ) / 4)⟯ = 4 :=
  adjoin_nthRoot_finrank 4 30 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end CubeRoot2IrrationalOQ03
