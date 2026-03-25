# Erdős #1179 OQ-01: Second-Order Term in g_ε(N)

## Problem Summary

For ε > 0, g_ε(N) is the smallest k such that a random k-subset of ℤ/Nℤ
has approximately uniform representation counts. Known: g_ε(N) ~ log₂ N.
Open question: what is the precise second-order correction term?

**File**: `proofs/Proofs/Erdos1179OQ01.lean`
**Status**: 1 axiom, 0 sorries, 11 theorems, 286 lines

## Session 2026-03-25 (Session 1) - Fix false axiom, prove erdos_renyi_decay

**Mode**: FRESH
**Outcome**: progress (1 axiom eliminated, 1 false axiom corrected)

### What I Did
- Discovered `fourier_error_bound` axiom was **mathematically false**
  - Counterexample: A = {1,2} ⊆ ℤ/3ℤ gives error 2/3 but old bound was 1/2
  - Missing `2^k/p` scaling factor in the bound
  - Need `k-1` exponent (not `k`) to handle 0 ∈ A where |cos(0)| = 1
- Corrected the axiom: `|(F_A(g) - 2^k/p| ≤ (p-1)·|cos(π/p)|^(k-1)·(2^k/p)`
- **Proved `erdos_renyi_decay`** as a theorem (was axiom):
  - Key insight: relative error is `(p-1)·|cos(π/p)|^(k-1)` which → 0 geometrically
  - Used `exists_pow_lt_of_lt_one` to find threshold K₀
  - Used `pow_le_pow_of_le_one` for monotonic decay
- Proved helper `abs_cos_pi_div_prime_lt_one` via `Real.strictAntiOn_cos`
- Docker build verified: 0 errors, 0 sorries, 1 axiom

### Key Findings
- The Fourier bound in the 2^k/p factor cancels when computing relative error, making erdos_renyi_decay a clean consequence
- `Real.strictAntiOn_cos` on `Set.Icc 0 π` is the right tool for proving |cos(x)| < 1 for 0 < x < π
- Import paths: `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` (not `.Order`) and `Mathlib.Analysis.SpecificLimits.Normed` (not `.Basic`)

### Files Modified
- `proofs/Proofs/Erdos1179OQ01.lean` (213 → 286 lines, 2 → 1 axiom)
- `src/data/proofs/erdos-1179-oq-01/meta.json` (updated counts)
- `src/data/research/problems/erdos-1179-oq-01.json` (updated knowledge)

### Next Steps
- Prove `fourier_error_bound` from Mathlib character theory (requires AddChar infrastructure)
- Formalize Θ(log log N) ⟹ o(log N) to complete the hierarchy chain
