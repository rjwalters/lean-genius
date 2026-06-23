/-
# [ℚ(∛3):ℚ] = 3 as Corollary of Eisenstein Approach

**Open Question OQ-01** from `cube-root-3-irrational-oq-02`:
Can [ℚ(∛3):ℚ] = 3 be derived as a corollary of the Eisenstein criterion proof?

## Answer: Yes — one-line corollary

`CubeRoot2IrrationalOQ03` already proves the general theorem:

  `adjoin_nthRoot_finrank n m p hn hp hdvd hndvd hm :`
  `  Module.finrank ℚ ℚ⟮(m:ℝ)^(1/n)⟯ = n`

when m has a prime factor p with p | m but p² ∤ m.

Specializing to n=3, m=3, p=3 (since 3 | 3 but 9 ∤ 3) immediately gives [ℚ(∛3):ℚ] = 3.

## What This File Proves

1. **Field extension degree**: [ℚ(∛3):ℚ] = 3 (corollary of general theorem)
2. **Minimal polynomial degree**: natDegree(minpoly ℚ ∛3) = 3 (same corollary route)
3. **Irrationality from degree**: ∛3 ∉ ℚ re-derived: if ∛3 = q ∈ ℚ then
   minpoly ℚ ∛3 = X - C q (degree 1), contradicting degree 3
4. **General principle**: for algebraic α, [ℚ(α):ℚ] > 1 implies α ∉ ℚ

## Mathematical Significance

The degree [ℚ(∛3):ℚ] = 3 is strictly stronger than mere irrationality:

- **Irrationality** only requires degree > 1: ∛3 ∉ ℚ
- **Degree 3** means no quadratic rational relation: there exist no q, r ∈ ℚ
  with (∛3)² = q + r · ∛3 (such an equation would give a degree-2 polynomial
  over ℚ vanishing at ∛3, contradicting minpoly degree = 3)
- **Basis certificate**: {1, ∛3, (∛3)²} is a ℚ-basis for ℚ(∛3)
  (open question OQ-02 proves linear independence directly)

## Status: 0 sorries, 0 axioms
-/

import Proofs.CubeRoot2IrrationalOQ03

open Polynomial CubeRoot2IrrationalOQ03 IntermediateField

namespace CubeRoot3IrrationalOQ02OQ01

-- ============================================================
-- PART I: FIELD EXTENSION DEGREE [ℚ(∛3):ℚ] = 3
-- ============================================================

/-- **[ℚ(∛3):ℚ] = 3** — the field extension has degree 3.

    Direct corollary of `adjoin_nthRoot_finrank` with n=3, m=3, p=3:
    - 3 | 3 (constant term is 3, divisible by p=3) ✓
    - 9 ∤ 3 (so p² ∤ m) ✓
    - 0 < 3 ✓

    The Eisenstein criterion makes X³-3 irreducible over ℚ, so its degree
    equals the extension degree [ℚ(∛3):ℚ] = natDegree(X³-3) = 3. -/
theorem cbrt3_fieldExtDegree :
    Module.finrank ℚ ℚ⟮(3 : ℝ) ^ ((1 : ℝ) / 3)⟯ = 3 :=
  adjoin_nthRoot_finrank 3 3 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

-- ============================================================
-- PART II: MINIMAL POLYNOMIAL DEGREE
-- ============================================================

/-- The minimal polynomial of ∛3 over ℚ has natDegree 3.

    Corollary of `minpoly_nthRoot_natDegree` (n=3, m=3, p=3): X³-3 is
    the minimal polynomial (irreducible via Eisenstein, monic, vanishes at ∛3). -/
theorem minpoly_cbrt3_natDeg :
    (minpoly ℚ ((3 : ℝ) ^ ((1 : ℝ) / 3))).natDegree = 3 :=
  minpoly_nthRoot_natDegree 3 3 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

-- ============================================================
-- PART III: IRRATIONALITY FROM DEGREE
-- ============================================================

/-- **Irrationality of ∛3 via field degree**: ∛3 ∉ ℚ.

    **Proof via minimal polynomial**:
    Suppose ∛3 = q ∈ ℚ. Then `minpoly ℚ ∛3 = X - C q` (degree 1), since q is in
    the base field. But `minpoly ℚ ∛3 = X³ - 3` has degree 3. Contradiction.

    **Third proof of ∛3 irrationality**:
    - `CubeRoot3Irrational.lean`: direct — 3 is not a perfect cube (integer bounds)
    - `CubeRoot3IrrationalOQ02.lean`: Eisenstein — X³-3 irreducible, no rational roots
    - **This file**: degree — [ℚ(∛3):ℚ] = 3 > 1, so ∛3 ∉ ℚ -/
theorem cbrt3_irrational_from_degree :
    Irrational ((3 : ℝ) ^ ((1 : ℝ) / 3)) := by
  intro h
  obtain ⟨q, hq⟩ := h
  -- If ∛3 = q ∈ ℚ, then minpoly ℚ ∛3 = X - C q (degree 1)
  have hmin : minpoly ℚ ((3 : ℝ) ^ ((1 : ℝ) / 3)) = X - C q := by
    rw [← hq]; exact minpoly.eq_X_sub_C ℚ q
  -- But minpoly ℚ ∛3 has degree 3
  have hdeg3 := minpoly_cbrt3_natDeg
  rw [hmin, natDegree_X_sub_C] at hdeg3
  exact absurd hdeg3 (by norm_num)

-- ============================================================
-- PART IV: GENERAL PRINCIPLE
-- ============================================================

/-- **General principle**: if α is algebraic over ℚ with [ℚ(α):ℚ] > 1, then α ∉ ℚ.

    Proof: if α = q ∈ ℚ, then `minpoly ℚ α = X - C q` (degree 1), giving
    [ℚ(α):ℚ] = 1 by `IntermediateField.adjoin.finrank`. Contradicts hypothesis.

    This captures the fundamental link between field extension degree and
    transcendence over the base field: degree = 1 iff the element is in the base. -/
theorem irrational_of_degree_gt_one {α : ℝ} (hα : IsIntegral ℚ α)
    (hdeg : 1 < Module.finrank ℚ ℚ⟮α⟯) : Irrational α := by
  intro h
  obtain ⟨q, hq⟩ := h
  -- If α = q ∈ ℚ, then minpoly ℚ α = X - C q
  have hmin : minpoly ℚ α = X - C q := by
    rw [← hq]; exact minpoly.eq_X_sub_C ℚ q
  -- This gives [ℚ(α):ℚ] = deg(X - C q) = 1
  have h1 : Module.finrank ℚ ℚ⟮α⟯ = 1 := by
    rw [IntermediateField.adjoin.finrank hα, hmin, natDegree_X_sub_C]
  linarith

/-- **∛3 irrationality via the general principle**: applies `irrational_of_degree_gt_one`. -/
theorem cbrt3_irrational_via_principle :
    Irrational ((3 : ℝ) ^ ((1 : ℝ) / 3)) :=
  irrational_of_degree_gt_one
    (isIntegral_nthRoot 3 3 (by norm_num))
    (by rw [cbrt3_fieldExtDegree])

end CubeRoot3IrrationalOQ02OQ01
