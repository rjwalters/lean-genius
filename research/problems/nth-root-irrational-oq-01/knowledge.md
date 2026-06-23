# nth-root-irrational-oq-01: Knowledge

## Problem Summary

Extend nth-root irrationality to algebraic irrationality via irreducible polynomials.
The base `NthRootIrrational.lean` uses a counting argument; OQ-01 provides a structural
approach via Eisenstein's criterion and the Gauss lemma.

**Status**: COMPLETE (0 axioms, 0 sorries)

## Session 2026-03-12 (Session 1) - Eisenstein + Gauss Proof

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Identified the single axiom `eisenstein_X_pow_sub_prime` as the target
- Found Mathlib APIs: `Polynomial.irreducible_of_eisenstein_criterion` and `IsPrimitive.Int.irreducible_iff_irreducible_map_cast`
- Proved irreducibility over ℤ via Eisenstein at prime ideal (p) with 6 subgoals
- Transferred to ℚ via Gauss lemma using `convert` + `ext` + `simp`
- Fixed multiple API issues through 4 build iterations
- Final result: 10 theorems, 0 axioms, 0 sorries

### Key Findings
- Eisenstein criterion requires 6 goals: prime ideal, leading coeff ∉ P, lower coeffs ∈ P, positive degree, constant coeff ∉ P², isPrimitive
- Gauss lemma: `IsPrimitive` is a `def` not a `structure` — dot notation fails; use fully qualified function call
- `coeff_X_pow` gives `if k = n` (index first), not `if n = k`
- `leadingCoeff_X_pow_sub_C` and `degree_X_pow_sub_C` take `(0 < n)`, `monic_X_pow_sub_C` takes `(n ≠ 0)`
- p² ∤ p proof: `Int.le_of_dvd` + `nlinarith [sq_nonneg ((p:ℤ) - 1)]`

### Files Modified
- `proofs/Proofs/NthRootIrrationalOQ01.lean` — eliminated axiom, all theorems proved

### Next Steps
- None — problem complete
