import Mathlib
import Proofs.CubeRoot2IrrationalOQ03

open Polynomial IntermediateField CubeRoot2IrrationalOQ03

set_option maxHeartbeats 800000

/-
# Minimal Polynomial of √n over ℚ: Eisenstein Generalization

**Open Question (from sqrt2-minpoly-oq-01)**:

For which natural numbers n is `minpoly ℚ (Real.sqrt n) = X² - n`?

## Mathematical Answer

The identity holds whenever n has a prime factor p with p | n but p² ∤ n.
This Eisenstein condition at p is satisfied for:
- All squarefree n ≥ 2 (n = 2, 3, 5, 6, 7, 10, 11, ...)
- Any n = p^(2k+1) · m where m has a squarefree prime factor

**General case (Part VII)**: The identity holds for ALL non-perfect-squares n,
covering cases where Eisenstein fails (e.g. n = 8 = 2³, n = 27 = 3³).

## Status: 0 sorries, 0 axioms
-/

namespace Sqrt2MinpolyOQ01

/-! ## Part I: Bridging Real.sqrt and rpow -/

/-- `Real.sqrt n = (n : ℝ) ^ ((1 : ℝ) / (2 : ℕ))`, connecting the
    `Real.sqrt` API to the general nth-root rpow representation. -/
private lemma sqrt_eq_rpow_nat (n : ℕ) :
    Real.sqrt n = (n : ℝ) ^ ((1 : ℝ) / (2 : ℕ)) := by
  rw [Real.sqrt_eq_rpow]
  norm_cast

/-! ## Part II: Main Theorem — Squarefree Prime Factor Condition -/

/-- **Main Result**: The minimal polynomial of √n over ℚ is X² - n,
    when n has a prime factor p with p | n but p² ∤ n.

    This generalizes `minpoly ℚ (√2) = X² - 2` to all n satisfying
    the Eisenstein condition at some prime p. -/
theorem minpoly_sqrt_of_sqfree_factor (n p : ℕ) (hn : 0 < n)
    (hp : Nat.Prime p) (hdvd : p ∣ n) (hndvd : ¬ p ^ 2 ∣ n) :
    minpoly ℚ (Real.sqrt n) = X ^ 2 - C (n : ℚ) := by
  rw [sqrt_eq_rpow_nat]
  exact (minpoly_nthRoot_eq 2 n p (by norm_num) hp hdvd hndvd hn).symm

/-! ## Part III: Squarefree Corollary -/

/-- For squarefree n ≥ 2, there exists a prime factor p with p | n but p² ∤ n.
    Uses `Nat.squarefree_iff_prime_squarefree`: squarefree ↔ no prime square divides n. -/
private lemma squarefree_has_prime_sqfree_factor {n : ℕ} (hn : 1 < n)
    (hsf : Squarefree n) : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ ¬ p ^ 2 ∣ n := by
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  refine ⟨p, hp, hdvd, ?_⟩
  have h := Nat.squarefree_iff_prime_squarefree.mp hsf p hp
  rwa [sq]

/-- **Squarefree Corollary**: For squarefree n ≥ 2, `minpoly ℚ (√n) = X² - n`.
    Covers √2, √3, √5, √6, √7, √10, √11, √13, √14, √15, ... -/
theorem minpoly_sqrt_of_squarefree (n : ℕ) (hn : 1 < n) (hsf : Squarefree n) :
    minpoly ℚ (Real.sqrt n) = X ^ 2 - C (n : ℚ) := by
  obtain ⟨p, hp, hdvd, hndvd⟩ := squarefree_has_prime_sqfree_factor hn hsf
  exact minpoly_sqrt_of_sqfree_factor n p (by omega) hp hdvd hndvd

/-! ## Part IV: Degree and Extension Results -/

/-- The algebraic degree of √n over ℚ is 2, when n has a squarefree prime factor. -/
theorem minpoly_sqrt_natDegree (n p : ℕ) (hn : 0 < n)
    (hp : Nat.Prime p) (hdvd : p ∣ n) (hndvd : ¬ p ^ 2 ∣ n) :
    (minpoly ℚ (Real.sqrt n)).natDegree = 2 := by
  rw [minpoly_sqrt_of_sqfree_factor n p hn hp hdvd hndvd]
  exact natDegree_X_pow_sub_nat_eq (by norm_num) hn.ne'

/-- The field extension degree [ℚ(√n) : ℚ] = 2, when n has a squarefree prime factor. -/
theorem adjoin_sqrt_finrank (n p : ℕ) (hn : 0 < n)
    (hp : Nat.Prime p) (hdvd : p ∣ n) (hndvd : ¬ p ^ 2 ∣ n) :
    Module.finrank ℚ ℚ⟮Real.sqrt n⟯ = 2 := by
  rw [sqrt_eq_rpow_nat]
  exact adjoin_nthRoot_finrank 2 n p (by norm_num) hp hdvd hndvd hn

/-! ## Part V: Non-Perfect-Square Corollary -/

/-- n has a squarefree prime factor iff n is not a perfect square.

    More precisely: p | n but p² ∤ n implies n is not a perfect square.
    (The converse holds for squarefree n.) -/
theorem not_perfect_square_of_sqfree_factor (n p : ℕ)
    (hp : Nat.Prime p) (hdvd : p ∣ n) (hndvd : ¬ p ^ 2 ∣ n) :
    ¬ ∃ k : ℕ, n = k ^ 2 := by
  exact not_perfect_power_of_sqfree_factor 2 n p (by norm_num) hp hdvd hndvd


/-! ## Part VI: Concrete Examples -/

/-- √2: minpoly ℚ (√2) = X² - 2 -/
theorem minpoly_sqrt_two : minpoly ℚ (Real.sqrt 2) = X ^ 2 - C 2 :=
  minpoly_sqrt_of_sqfree_factor 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- √3: minpoly ℚ (√3) = X² - 3 -/
theorem minpoly_sqrt_three : minpoly ℚ (Real.sqrt 3) = X ^ 2 - C 3 :=
  minpoly_sqrt_of_sqfree_factor 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- √5: minpoly ℚ (√5) = X² - 5 -/
theorem minpoly_sqrt_five : minpoly ℚ (Real.sqrt 5) = X ^ 2 - C 5 :=
  minpoly_sqrt_of_sqfree_factor 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- √6: minpoly ℚ (√6) = X² - 6  (p=2: 2|6 but 4∤6) -/
theorem minpoly_sqrt_six : minpoly ℚ (Real.sqrt 6) = X ^ 2 - C 6 :=
  minpoly_sqrt_of_sqfree_factor 6 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- √7: minpoly ℚ (√7) = X² - 7 -/
theorem minpoly_sqrt_seven : minpoly ℚ (Real.sqrt 7) = X ^ 2 - C 7 :=
  minpoly_sqrt_of_sqfree_factor 7 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- √10: minpoly ℚ (√10) = X² - 10  (p=2: 2|10 but 4∤10) -/
theorem minpoly_sqrt_ten : minpoly ℚ (Real.sqrt 10) = X ^ 2 - C 10 :=
  minpoly_sqrt_of_sqfree_factor 10 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- √12: minpoly ℚ (√12) = X² - 12  (p=3: 3|12 but 9∤12) -/
theorem minpoly_sqrt_twelve : minpoly ℚ (Real.sqrt 12) = X ^ 2 - C 12 :=
  minpoly_sqrt_of_sqfree_factor 12 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- √20: minpoly ℚ (√20) = X² - 20  (p=5: 5|20 but 25∤20) -/
theorem minpoly_sqrt_twenty : minpoly ℚ (Real.sqrt 20) = X ^ 2 - C 20 :=
  minpoly_sqrt_of_sqfree_factor 20 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Part VII: General Case — All Non-Perfect-Square Natural Numbers

The Eisenstein condition (p | n but p² ∤ n) is strictly weaker than ¬IsSquare n.
Example: n = 8 = 2³ satisfies ¬IsSquare 8 (√8 = 2√2 is irrational), but
4 | 8, so no Eisenstein prime exists.

Strategy:
1. Irrational (Real.sqrt n) when ¬IsSquare n (via irrational_nrt_of_notint_nrt)
2. Irrationality → minpoly degree ≥ 2 (degree 1 would force Real.sqrt n ∈ ℚ)
3. minpoly | X² - n → degree ≤ 2
4. Both monic degree 2 with minpoly | X²-n → equal
-/

/-- If n is not a perfect square, Real.sqrt n is irrational. -/
private lemma irrational_sqrt_of_not_sq {n : ℕ} (hn : 0 < n) (hns : ¬ IsSquare n) :
    Irrational (Real.sqrt n) := by
  rw [sqrt_eq_rpow_nat]
  apply irrational_nrt_of_notint_nrt 2 n
  · -- ((n : ℝ)^(1/2))^2 = n
    rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / (2 : ℕ))) 2,
        ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  · -- Not an integer: k² = n would give IsSquare n, contradicting hns
    intro ⟨k, hk⟩
    apply hns
    have hk2 : k ^ 2 = (n : ℤ) := by
      have hrpow : ((n : ℝ) ^ ((1 : ℝ) / (2 : ℕ))) ^ 2 = (n : ℝ) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / (2 : ℕ))) 2,
            ← Real.rpow_mul (Nat.cast_nonneg n)]
        norm_num
      rw [← hk] at hrpow
      exact_mod_cast hrpow
    refine ⟨k.natAbs, ?_⟩
    have habs : k.natAbs ^ 2 = n := by
      have h1 := Int.natAbs_pow k 2
      rw [hk2, Int.natAbs_ofNat] at h1
      omega
    linarith [show k.natAbs * k.natAbs = k.natAbs ^ 2 from by ring]
  · norm_num

/-- **General Theorem**: `minpoly ℚ (Real.sqrt n) = X² - n` for ALL non-perfect-square n.

    This strictly generalizes the Eisenstein-based Parts II–III:
    - n = 8 = 2³: ¬IsSquare 8, Eisenstein fails (4|8), covered here ✓
    - n = 27 = 3³: ¬IsSquare 27, Eisenstein fails (9|27), covered here ✓
    - n = 32 = 2⁵: ¬IsSquare 32, Eisenstein fails (4|32), covered here ✓ -/
theorem minpoly_sqrt_of_not_sq (n : ℕ) (hn : 0 < n) (hns : ¬ IsSquare n) :
    minpoly ℚ (Real.sqrt n) = X ^ 2 - C (n : ℚ) := by
  have hXn_monic : (X ^ 2 - C (n : ℚ) : ℚ[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hXn_aeval : Polynomial.aeval (Real.sqrt n) (X ^ 2 - C (n : ℚ) : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    push_cast
    linarith [Real.sq_sqrt (show (0 : ℝ) ≤ n by exact_mod_cast hn.le)]
  have hintegral : IsIntegral ℚ (Real.sqrt n) :=
    ⟨X ^ 2 - C (n : ℚ), hXn_monic, hXn_aeval⟩
  have hdvd : minpoly ℚ (Real.sqrt n) ∣ X ^ 2 - C (n : ℚ) :=
    minpoly.dvd ℚ (Real.sqrt n) hXn_aeval
  have hXn_ne : (X ^ 2 - C (n : ℚ) : ℚ[X]) ≠ 0 := Polynomial.Monic.ne_zero hXn_monic
  have hdeg_le : (minpoly ℚ (Real.sqrt n)).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd hdvd hXn_ne
    simpa [Polynomial.natDegree_X_pow_sub_C] using this
  have hirr : Irrational (Real.sqrt n) := irrational_sqrt_of_not_sq hn hns
  have hdeg_ge : 2 ≤ (minpoly ℚ (Real.sqrt n)).natDegree := by
    by_contra hlt
    push_neg at hlt
    have hdeg1 : (minpoly ℚ (Real.sqrt n)).natDegree = 1 := by
      have hge1 := minpoly.natDegree_pos hintegral; omega
    obtain ⟨a, b, ha, hfab⟩ := Polynomial.natDegree_eq_one.mp hdeg1
    have hmonic := minpoly.monic hintegral
    have ha1 : a = 1 := by
      have hlc := hmonic.leadingCoeff
      rw [hfab] at hlc
      simp [Polynomial.leadingCoeff_add_of_degree_lt, Polynomial.degree_C_mul_X ha,
            Polynomial.degree_C, ha] at hlc
      exact hlc
    rw [ha1, one_mul] at hfab
    have heval := minpoly.aeval ℚ (Real.sqrt n)
    rw [hfab] at heval
    simp only [map_add, aeval_X, aeval_C] at heval
    exact hirr ⟨-b, by push_cast at heval ⊢; linarith⟩
  have hdeg : (minpoly ℚ (Real.sqrt n)).natDegree = 2 := Nat.le_antisymm hdeg_le hdeg_ge
  obtain ⟨c, hc⟩ := hdvd
  have hc_ne : c ≠ 0 := by intro hc0; simp [hc0] at hc; exact hXn_ne hc
  have hc_deg : c.natDegree = 0 := by
    have hmul_deg := Polynomial.natDegree_mul (minpoly.ne_zero hintegral) hc_ne
    rw [← hc, Polynomial.natDegree_X_pow_sub_C, hdeg] at hmul_deg
    omega
  have hc_one : c = 1 := by
    have hmul_lc : (minpoly ℚ (Real.sqrt n) * c).leadingCoeff = 1 := by
      rw [← hc]; exact hXn_monic.leadingCoeff
    rw [Polynomial.leadingCoeff_mul, (minpoly.monic hintegral).leadingCoeff, one_mul] at hmul_lc
    have hc_const := Polynomial.eq_C_of_natDegree_eq_zero hc_deg
    rw [hc_const, Polynomial.leadingCoeff_C] at hmul_lc
    rw [hc_const, hmul_lc, map_one]
  rw [hc_one, mul_one] at hc
  exact hc.symm

/-! ## Part VII Corollaries: Examples Not Covered by Eisenstein -/

/-- √8 = 2√2: minpoly ℚ (√8) = X² - 8. (n=8=2³: Eisenstein fails since 4|8) -/
theorem minpoly_sqrt_eight : minpoly ℚ (Real.sqrt 8) = X ^ 2 - C 8 :=
  minpoly_sqrt_of_not_sq 8 (by norm_num) (by
    rintro ⟨k, hk⟩
    have hk_le : k ≤ 3 := by nlinarith
    interval_cases k <;> simp_all)

/-- √27 = 3√3: minpoly ℚ (√27) = X² - 27. (n=27=3³: Eisenstein fails since 9|27) -/
theorem minpoly_sqrt_twentyseven : minpoly ℚ (Real.sqrt 27) = X ^ 2 - C 27 :=
  minpoly_sqrt_of_not_sq 27 (by norm_num) (by
    rintro ⟨k, hk⟩
    have hk_le : k ≤ 5 := by nlinarith
    interval_cases k <;> simp_all)

/-- √32 = 4√2: minpoly ℚ (√32) = X² - 32. (n=32=2⁵: Eisenstein fails since 4|32) -/
theorem minpoly_sqrt_thirtytwo : minpoly ℚ (Real.sqrt 32) = X ^ 2 - C 32 :=
  minpoly_sqrt_of_not_sq 32 (by norm_num) (by
    rintro ⟨k, hk⟩
    have hk_le : k ≤ 6 := by nlinarith
    interval_cases k <;> simp_all)

end Sqrt2MinpolyOQ01
