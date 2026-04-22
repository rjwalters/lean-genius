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

## Key Insight

The proof bridges two representations of the square root:
  `Real.sqrt n = (n : ℝ) ^ ((1 : ℝ) / 2)`
via `Real.sqrt_eq_rpow`, then applies the general `minpoly_nthRoot_eq`
theorem (from CubeRoot2IrrationalOQ03) with degree 2.

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

end Sqrt2MinpolyOQ01
