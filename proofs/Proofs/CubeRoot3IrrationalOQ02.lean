/-
# Cube Root of 3 Irrationality: Eisenstein Criterion Approach

**Open Question OQ-02** from `cube-root-3-irrational`:
Give an algebraic proof of ∛3's irrationality using Eisenstein's irreducibility criterion,
rather than the direct `irrational_nrt_of_notint_nrt` approach.

## Mathematical Strategy

1. **Eisenstein at p = 3**: X³ - 3 is irreducible over ℚ.
   (3 | constant term -3, 9 ∤ -3, 3 ∤ leading coefficient 1)

2. **No rational roots**: An irreducible polynomial of degree > 1 has no roots in ℚ.
   If q ∈ ℚ is a root, then (X - C q) | (X³ - 3). Since X³ - 3 is irreducible
   and (X - C q) is not a unit (degree 1), we need X³ - 3 = (X - C q) · (unit),
   giving natDegree 1 ≠ 3. Contradiction.

3. **Irrationality**: If ∛3 = q ∈ ℚ, then q³ = 3, making q a rational root of X³ - 3.
   Contradiction with step 2.

## Relationship to Gallery
- **CubeRoot3Irrational.lean**: uses `irrational_nrt_of_notint_nrt` (check no perfect cube)
- **CubeRoot2IrrationalOQ03.lean**: general algebraic degree theory, used as dependency here
- **This file**: Eisenstein → irreducibility → no rational roots → irrationality

## Status: 0 sorries
-/

import Proofs.CubeRoot2IrrationalOQ03
import Mathlib.Data.Real.Irrational

open Polynomial CubeRoot2IrrationalOQ03

namespace CubeRoot3IrrationalOQ02

-- ============================================================
-- PART 1: X³ - 3 is irreducible over ℚ (Eisenstein at p = 3)
-- ============================================================

/-- X³ - 3 is irreducible over ℚ by Eisenstein's criterion at p = 3.

The prime p = 3 satisfies the Eisenstein conditions for X³ - 3:
- 3 | 3 (constant term is divisible by 3) ✓
- 9 ∤ 3 (constant term not divisible by 3²) ✓
- 3 ∤ 1 (leading coefficient not divisible by 3) ✓ -/
theorem X3_sub_3_irred : Irreducible (X ^ 3 - C 3 : ℚ[X]) :=
  eisenstein_X_pow_sub_of_sqfree_factor 3 3 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

-- ============================================================
-- PART 2: X³ - 3 has no rational roots
-- ============================================================

/-- The polynomial X³ - 3 evaluates to a nonzero value at every rational number.

**Proof**: Suppose q : ℚ is a root (eval q (X³ - 3) = 0).
Then (X - C q) ∣ (X³ - 3) by `dvd_iff_isRoot`.
Write X³ - 3 = (X - C q) · R. Since X³ - 3 is irreducible:
- **Case `IsUnit (X - C q)`**: but natDegree(X - C q) = 1 > 0 = natDegree of any unit.
- **Case `IsUnit R`**: then natDegree(X³ - 3) = natDegree(X - C q) + 0 = 1 ≠ 3. -/
theorem X3_sub_3_no_rat_root (q : ℚ) : (X ^ 3 - C 3 : ℚ[X]).eval q ≠ 0 := by
  intro hroot
  -- (X - C q) divides X³ - 3
  have hdvd : (X - C q) ∣ (X ^ 3 - C 3 : ℚ[X]) := dvd_iff_isRoot.mpr hroot
  obtain ⟨R, hR⟩ := hdvd
  -- Compute natDegree of X³ - 3 = 3
  have hlt : (C 3 : ℚ[X]).natDegree < (X ^ 3 : ℚ[X]).natDegree := by
    simp [natDegree_C, natDegree_pow, natDegree_X]
  have hpoly3 : (X ^ 3 - C 3 : ℚ[X]).natDegree = 3 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt hlt, natDegree_pow, natDegree_X, mul_one]
  -- Invoke irreducibility on the factorization X³ - 3 = (X - C q) * R
  cases X3_sub_3_irred.isUnit_or_isUnit hR with
  | inl h =>
    -- X - C q is a unit: impossible since its natDegree = 1
    have hd := Polynomial.natDegree_eq_zero_of_isUnit h
    have hd1 : (X - C q : ℚ[X]).natDegree = 1 := natDegree_X_sub_C q
    omega
  | inr h =>
    -- R is a unit: so natDegree R = 0, giving natDegree(X³-3) = 1 + 0 = 1 ≠ 3
    have hR_deg : R.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit h
    have hq_ne : (X - C q : ℚ[X]) ≠ 0 := X_sub_C_ne_zero q
    have hR_ne : R ≠ 0 := by
      rintro rfl; simp at hR; exact absurd hR.symm (by simp [hpoly3])
    have hmul_deg : ((X - C q) * R).natDegree = 1 := by
      rw [natDegree_mul hq_ne hR_ne, natDegree_X_sub_C, hR_deg]
    rw [← hR, hpoly3] at hmul_deg
    norm_num at hmul_deg

-- ============================================================
-- PART 3: Irrationality of ∛3 via Eisenstein
-- ============================================================

/-- ∛3 is irrational, proved via the Eisenstein irreducibility criterion.

**Proof**:
1. By Eisenstein at p = 3: X³ - 3 is irreducible over ℚ.
2. Irreducible degree-3 polynomials have no rational roots (proved above).
3. If ∛3 = q ∈ ℚ, then q³ = 3, so q is a rational root of X³ - 3.
4. Contradiction with step 2.

**Contrast with CubeRoot3Irrational.lean**: The original proof uses
`irrational_nrt_of_notint_nrt`, which checks that 3 is not a perfect cube.
This proof gives a more algebraically systematic approach via polynomial
irreducibility, which generalizes to show X³ - 3 has no rational roots at all
(not just that its roots are not integers). -/
theorem cbrt3_irrational_via_eisenstein : Irrational ((3 : ℝ) ^ ((1 : ℝ) / 3)) := by
  -- Suppose (3:ℝ)^(1/3) ∈ ℚ, i.e., ∃ q : ℚ, (↑q : ℝ) = (3:ℝ)^(1/3)
  intro ⟨q, hq⟩
  -- hq : (↑q : ℝ) = (3:ℝ)^(1/3)
  -- Step 1: q³ = 3 as reals
  have hq3_real : (q : ℝ) ^ 3 = 3 := by
    rw [hq, ← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 3)) 3,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  -- Step 2: q³ = 3 as rationals (by injectivity of ℚ ↪ ℝ)
  have hq3 : q ^ 3 = 3 := by exact_mod_cast hq3_real
  -- Step 3: q is a root of X³ - 3 over ℚ
  have heval : (X ^ 3 - C 3 : ℚ[X]).eval q = 0 := by
    simp [eval_sub, eval_pow, eval_X, eval_C, hq3]
  -- Step 4: contradiction with X3_sub_3_no_rat_root
  exact X3_sub_3_no_rat_root q heval

end CubeRoot3IrrationalOQ02
