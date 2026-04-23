import Mathlib
import Proofs.CubeRoot2IrrationalOQ03

open Polynomial IntermediateField CubeRoot2IrrationalOQ03

set_option maxHeartbeats 800000

/-
# Minimal Polynomial of k-th Roots: minpoly ℚ (m^(1/k)) = Xᵏ - m via Eisenstein

**Open Question (from sqrt2-minpoly-oq-02)**:

For which natural numbers m and k ≥ 2 is `minpoly ℚ (m^(1/k)) = Xᵏ - m`?

## Mathematical Answer

The identity holds whenever m has a prime factor p with p | m but p² ∤ m.
This is the **squarefree prime factor condition** (Eisenstein criterion at p).

It applies for:
- All squarefree m ≥ 2: ∛2, ∛3, ∛5, ⁴√2, ⁵√7, ...
- Non-squarefree m with a "squarefree prime": e.g. m = 12 (p=3: 3|12, 9∤12)

## Architecture

This file builds on `CubeRoot2IrrationalOQ03` which proves the general
`minpoly_nthRoot_eq` theorem. This file adds:

1. A squarefree corollary for general k (all squarefree m ≥ 2, all k ≥ 2)
2. Irrationality as a corollary
3. Concrete examples for cube roots, fourth roots, fifth roots

## Status: 0 sorries, 0 axioms
-/

namespace Sqrt2MinpolyOQ02

/-! ## Part I: Squarefree Auxiliary Lemma -/

/-- A squarefree m ≥ 2 has a prime factor p with p | m but p² ∤ m.
    This is the Eisenstein condition required for Xᵏ - m to be irreducible. -/
private lemma squarefree_has_prime_sqfree_factor {m : ℕ} (hm : 1 < m)
    (hsf : Squarefree m) : ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ ¬ p ^ 2 ∣ m := by
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  refine ⟨p, hp, hdvd, ?_⟩
  have h := Nat.squarefree_iff_prime_squarefree.mp hsf p hp
  rwa [sq]

/-! ## Part II: Main Theorems — Squarefree Prime Factor Condition -/

/-- **Main Result**: The minimal polynomial of m^(1/k) over ℚ is Xᵏ - m,
    when m has a prime factor p with p | m but p² ∤ m.

    This is the general Eisenstein result for all k ≥ 2, covering:
    - Cube roots: ∛2, ∛3, ∛5, ∛6, ∛7, ∛10, ...
    - Fourth roots: ⁴√2, ⁴√3, ⁴√5, ⁴√6, ...
    - Fifth roots: ⁵√2, ⁵√3, ⁵√5, ...
    - And all k ≥ 2. -/
theorem minpoly_kthRoot_of_sqfree_factor (k m p : ℕ) (hk : 2 ≤ k) (hm : 0 < m)
    (hp : Nat.Prime p) (hdvd : p ∣ m) (hndvd : ¬ p ^ 2 ∣ m) :
    minpoly ℚ ((m : ℝ) ^ ((1 : ℝ) / k)) = X ^ k - C (m : ℚ) :=
  (minpoly_nthRoot_eq k m p hk hp hdvd hndvd hm).symm

/-- **Squarefree Corollary**: For all squarefree m ≥ 2 and all k ≥ 2,
    `minpoly ℚ (m^(1/k)) = Xᵏ - m`.

    The Eisenstein condition is automatically satisfied for squarefree m:
    any prime p dividing m has p | m but p² ∤ m (by squarefreeness). -/
theorem minpoly_kthRoot_of_squarefree (k m : ℕ) (hk : 2 ≤ k) (hm : 1 < m)
    (hsf : Squarefree m) :
    minpoly ℚ ((m : ℝ) ^ ((1 : ℝ) / k)) = X ^ k - C (m : ℚ) := by
  obtain ⟨p, hp, hdvd, hndvd⟩ := squarefree_has_prime_sqfree_factor hm hsf
  exact minpoly_kthRoot_of_sqfree_factor k m p hk (by omega) hp hdvd hndvd

/-! ## Part III: Algebraic Degree and Field Extension -/

/-- The algebraic degree of m^(1/k) over ℚ is k,
    when m has a squarefree prime factor. -/
theorem minpoly_kthRoot_natDegree (k m p : ℕ) (hk : 2 ≤ k) (hm : 0 < m)
    (hp : Nat.Prime p) (hdvd : p ∣ m) (hndvd : ¬ p ^ 2 ∣ m) :
    (minpoly ℚ ((m : ℝ) ^ ((1 : ℝ) / k))).natDegree = k := by
  rw [minpoly_kthRoot_of_sqfree_factor k m p hk hm hp hdvd hndvd]
  exact natDegree_X_pow_sub_nat_eq (by omega) hm.ne'

/-- **Field Extension Degree**: [ℚ(m^(1/k)) : ℚ] = k,
    when m has a squarefree prime factor. -/
theorem adjoin_kthRoot_finrank (k m p : ℕ) (hk : 2 ≤ k) (hm : 0 < m)
    (hp : Nat.Prime p) (hdvd : p ∣ m) (hndvd : ¬ p ^ 2 ∣ m) :
    Module.finrank ℚ ℚ⟮(m : ℝ) ^ ((1 : ℝ) / ↑k)⟯ = k :=
  adjoin_nthRoot_finrank k m p hk hp hdvd hndvd hm

/-! ## Part IV: Non-Perfect-Power Criterion -/

/-- m^(1/k) with a squarefree prime factor implies m is not a perfect k-th power. -/
theorem not_perfect_kthPower_of_sqfree_factor (k m p : ℕ) (hk : 2 ≤ k)
    (hp : Nat.Prime p) (hdvd : p ∣ m) (hndvd : ¬ p ^ 2 ∣ m) :
    ¬ ∃ n : ℕ, m = n ^ k :=
  not_perfect_power_of_sqfree_factor k m p hk hp hdvd hndvd

/-! ## Part V: Concrete Examples -/

/-! ### Cube Roots (k = 3) -/

/-- ∛2: minpoly ℚ (∛2) = X³ - 2  [Eisenstein at p = 2] -/
theorem minpoly_cbrt_two :
    minpoly ℚ ((2 : ℝ) ^ ((1 : ℝ) / 3)) = X ^ 3 - C 2 :=
  minpoly_kthRoot_of_sqfree_factor 3 2 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- ∛3: minpoly ℚ (∛3) = X³ - 3  [Eisenstein at p = 3] -/
theorem minpoly_cbrt_three :
    minpoly ℚ ((3 : ℝ) ^ ((1 : ℝ) / 3)) = X ^ 3 - C 3 :=
  minpoly_kthRoot_of_sqfree_factor 3 3 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- ∛5: minpoly ℚ (∛5) = X³ - 5  [Eisenstein at p = 5] -/
theorem minpoly_cbrt_five :
    minpoly ℚ ((5 : ℝ) ^ ((1 : ℝ) / 3)) = X ^ 3 - C 5 :=
  minpoly_kthRoot_of_sqfree_factor 3 5 5 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- ∛6: minpoly ℚ (∛6) = X³ - 6  [Eisenstein at p = 2: 2|6, 4∤6] -/
theorem minpoly_cbrt_six :
    minpoly ℚ ((6 : ℝ) ^ ((1 : ℝ) / 3)) = X ^ 3 - C 6 :=
  minpoly_kthRoot_of_sqfree_factor 3 6 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- ∛7: minpoly ℚ (∛7) = X³ - 7  [Eisenstein at p = 7] -/
theorem minpoly_cbrt_seven :
    minpoly ℚ ((7 : ℝ) ^ ((1 : ℝ) / 3)) = X ^ 3 - C 7 :=
  minpoly_kthRoot_of_sqfree_factor 3 7 7 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-! ### Fourth Roots (k = 4) -/

/-- ⁴√2: minpoly ℚ (⁴√2) = X⁴ - 2  [Eisenstein at p = 2] -/
theorem minpoly_fourthrt_two :
    minpoly ℚ ((2 : ℝ) ^ ((1 : ℝ) / 4)) = X ^ 4 - C 2 :=
  minpoly_kthRoot_of_sqfree_factor 4 2 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- ⁴√3: minpoly ℚ (⁴√3) = X⁴ - 3  [Eisenstein at p = 3] -/
theorem minpoly_fourthrt_three :
    minpoly ℚ ((3 : ℝ) ^ ((1 : ℝ) / 4)) = X ^ 4 - C 3 :=
  minpoly_kthRoot_of_sqfree_factor 4 3 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- ⁴√5: minpoly ℚ (⁴√5) = X⁴ - 5  [Eisenstein at p = 5] -/
theorem minpoly_fourthrt_five :
    minpoly ℚ ((5 : ℝ) ^ ((1 : ℝ) / 4)) = X ^ 4 - C 5 :=
  minpoly_kthRoot_of_sqfree_factor 4 5 5 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- ⁴√30: minpoly ℚ (⁴√30) = X⁴ - 30  [Eisenstein at p = 2: 2|30, 4∤30]
    (This extends the ∜30 example from CubeRoot2IrrationalOQ03) -/
theorem minpoly_fourthrt_thirty :
    minpoly ℚ ((30 : ℝ) ^ ((1 : ℝ) / 4)) = X ^ 4 - C 30 :=
  minpoly_kthRoot_of_sqfree_factor 4 30 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-! ### Fifth Roots (k = 5) -/

/-- ⁵√2: minpoly ℚ (⁵√2) = X⁵ - 2  [Eisenstein at p = 2] -/
theorem minpoly_fifthrt_two :
    minpoly ℚ ((2 : ℝ) ^ ((1 : ℝ) / 5)) = X ^ 5 - C 2 :=
  minpoly_kthRoot_of_sqfree_factor 5 2 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- ⁵√3: minpoly ℚ (⁵√3) = X⁵ - 3  [Eisenstein at p = 3] -/
theorem minpoly_fifthrt_three :
    minpoly ℚ ((3 : ℝ) ^ ((1 : ℝ) / 5)) = X ^ 5 - C 3 :=
  minpoly_kthRoot_of_sqfree_factor 5 3 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- ⁵√12: minpoly ℚ (⁵√12) = X⁵ - 12  [Eisenstein at p = 3: 3|12, 9∤12]
    (Extends the ⁵√12 example from CubeRoot2IrrationalOQ03) -/
theorem minpoly_fifthrt_twelve :
    minpoly ℚ ((12 : ℝ) ^ ((1 : ℝ) / 5)) = X ^ 5 - C 12 :=
  minpoly_kthRoot_of_sqfree_factor 5 12 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-! ### Field Extension Degrees -/

/-- [ℚ(∛2) : ℚ] = 3 -/
theorem adjoin_cbrt_two_finrank :
    Module.finrank ℚ ℚ⟮(2 : ℝ) ^ ((1 : ℝ) / 3)⟯ = 3 :=
  adjoin_kthRoot_finrank 3 2 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- [ℚ(⁴√2) : ℚ] = 4 -/
theorem adjoin_fourthrt_two_finrank :
    Module.finrank ℚ ℚ⟮(2 : ℝ) ^ ((1 : ℝ) / 4)⟯ = 4 :=
  adjoin_kthRoot_finrank 4 2 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- [ℚ(⁵√3) : ℚ] = 5 -/
theorem adjoin_fifthrt_three_finrank :
    Module.finrank ℚ ℚ⟮(3 : ℝ) ^ ((1 : ℝ) / 5)⟯ = 5 :=
  adjoin_kthRoot_finrank 5 3 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end Sqrt2MinpolyOQ02
