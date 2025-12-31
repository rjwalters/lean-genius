# Research State: cube-root-2-irrational

## Current State
**Phase**: BREAKTHROUGH
**Since**: 2025-12-30T15:59:44-08:00
**Iteration**: 1

## Current Focus
PROOF SUCCESSFUL! Verifying and documenting results.

## Key Findings from OBSERVE

1. **Existing axioms found**:
   - `cbrt_two_irrational` in GelfondSchneider.lean (axiom, not proven)
   - `cube_doubling_impossible_axiom` in AngleTrisection.lean (axiom)

2. **Related proofs**:
   - `sqrt2-irrational`: Uses parity argument (won't work for cube roots)
   - Uses `Nat.Prime.irrational_sqrt` for primes
   - Uses `irrational_sqrt_natCast_iff` for general squares

3. **Proof strategies identified**:
   - Rational Root Theorem: x³ - 2 has no rational roots
   - Prime multiplicity: 3 doesn't divide 1
   - Eisenstein criterion: x³ - 2 is irreducible over ℚ

4. **Mathlib modules used**:
   - `Mathlib.Data.Real.Irrational` - `irrational_nrt_of_notint_nrt`
   - `Mathlib.Analysis.SpecialFunctions.Pow.Real` - `Real.rpow_mul`
   - `Mathlib.Tactic` - `nlinarith`, `omega`, `norm_num`

## SUCCESSFUL Approach
**approach-01**: Use `irrational_nrt_of_notint_nrt` theorem

### Key Insight
The theorem `irrational_nrt_of_notint_nrt` states:
- If x^n = m (integer) and x is not an integer, then x is irrational

For ∛2:
- x = 2^(1/3), n = 3, m = 2
- Need: (2^(1/3))^3 = 2 ✓
- Need: 2^(1/3) is not an integer ✓
- Therefore ∛2 is irrational ✓

### Technical Solution
To prove "2 is not a perfect cube" (no integer n with n³ = 2):
1. **Bound n > 0**: If n ≤ 0, then n³ ≤ 0 < 2 (contradiction)
2. **Bound n < 2**: If n ≥ 2, then n³ ≥ 8 > 2 (contradiction)
3. **Only n = 1 remains**: But 1³ = 1 ≠ 2 (contradiction)

Key tactic: Use `nlinarith` with `n³ = n * n * n` rewrite to handle cubic bounds.

## Attempt Log

| Attempt | Date | Result | Key Insight |
|---------|------|--------|-------------|
| 1 | 2025-12-30 | SUCCESS | Use nlinarith with n*n*n rewrite for cubic bounds |

## Proof Location
- **Research**: `research/problems/cube-root-2-irrational/approaches/approach-01/attempts/attempt-01.lean`
- **Gallery**: `proofs/Proofs/CubeRoot2Irrational.lean`

## Blockers
None - proof completed successfully!

## Next Action
1. ✓ Proof compiles successfully
2. Update hypothesis.md to mark lemmas as proven
3. Can now replace axiom `cbrt_two_irrational` in GelfondSchneider.lean
4. Document pattern for future n-th root irrationality proofs
