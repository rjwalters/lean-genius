# Erdős Problem #1131 OQ-01: Lagrange Basis Polynomial Integrals

## Problem Summary

For x₁,...,xₙ ∈ [-1,1], define Lagrange basis polynomials l_k(x) = ∏_{i≠k} (x - xᵢ)/(xₖ - xᵢ).
Find the minimum of I(x₁,...,xₙ) = ∫₋₁¹ Σₖ |l_k(x)|² dx.
Conjecture: min I = 2 - (1+o(1))/n.

## Current State
- **File**: `proofs/Proofs/Erdos1131Problem.lean` (306 lines)
- **Sorries**: 0
- **Axioms**: 2 (chebyshev_integral_estimate, erdos_1131_conjecture)
- **Theorems**: 9 (all fully proved)

## Session 2026-03-25 (Session 2) - Prove sorries, remove false axiom

**Mode**: REVISIT (MODERATE knowledge, score 12)
**Outcome**: progress

### What I Did
1. Proved `sum_sq_lagrangeBasis_ge` (∑ l_k² ≥ 1/n) via variance trick:
   - `suffices` to reduce to showing ∑l_k² - 1/n = ∑(l_k - 1/n)²
   - Expanded via `sub_sq`, split sum via `Finset.sum_add_distrib`/`sum_sub_distrib`
   - Factored middle sum via `Finset.mul_sum`, applied `hpou` (partition of unity)
   - Closed with `field_simp; ring`

2. Proved `lagrangeIntegral_lower_bound` (I ≥ 2/n) via integral monotonicity:
   - Showed integrand is continuous via `continuous_finset_sum` + `continuous_finset_prod`
   - Rewrote 2/n as ∫₋₁¹ 1/n dx
   - Used `intervalIntegral.integral_sub` + `intervalIntegral.integral_nonneg`

3. Removed false axiom `lagrangeIntegral_upper_bound` (I ≤ 2n):
   - **Counterexample**: n=2, nodes at 0 and δ give I = 2 + 4/(3δ²) → ∞ as δ → 0
   - No theorems depended on this axiom

### Key Findings
- `lagrangeIntegral_upper_bound` is mathematically false — no general upper bound on I exists
- `linarith` cannot recognize that `1/↑n` and `2/↑n` are linearly related; use `Finset.mul_sum` to factor first
- The `suffices` pattern (reduce goal to sum nonnegativity) is much cleaner than expanding and rearranging
- `field_simp; ring` handles the final arithmetic after clearing Finset.sum infrastructure

### Files Modified
- `proofs/Proofs/Erdos1131Problem.lean` (264→306 lines, 2→0 sorries, 3→2 axioms)
- `src/data/proofs/erdos-1131/meta.json`
- `src/data/research/problems/erdos-1131-oq-01.json`

### Next Steps
- `chebyshev_integral_estimate` requires Chebyshev polynomial T_n representation of l_k and exact integral computation — substantial infrastructure needed
- `erdos_1131_conjecture` is genuinely OPEN, stays as axiom
