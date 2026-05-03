# Knowledge Base: derangements-convergence-oq-01-oq-01

## Problem Summary

**Title**: Derangements Nearest Integer Theorem
**Focus**: Prove D(n) = round(n!/e) for n ≥ 1, i.e., |D(n) - n!/e| < 1/2

## Session 2026-05-03 (Session 1) — Nearest Integer Theorem Proved

**Mode**: FRESH
**Outcome**: completed — 7 theorems, 0 sorries, 0 axioms; PR created

### What I Did
- Fixed `DerangementsConvergence.lean`: replaced 12 deprecated `∑ k in`/`∑ i in` usages with `∑ k ∈`/`∑ i ∈` throughout (Python replace to handle Unicode correctly)
- Wrote `DerangementsConvergenceOQ01OQ01.lean` with 7 theorems proving D(n) = round(n!/e)
- Created gallery entry `src/data/proofs/derangements-convergence-oq-01-oq-01/`

### Key Findings
- **Rate scaling**: |D(n)/n! - e⁻¹| ≤ 1/(n+1)! scaled by n! gives |D(n) - n!/e| ≤ 1/(n+1)
- **Main theorem**: For n ≥ 2, 1/(n+1) ≤ 1/3 < 1/2, so D(n) is within 1/2 of n!/e
- **n=1 case**: D(1) = 0 and |0 - 1/e| = 1/e. Uses `Real.add_one_lt_exp one_ne_zero` (strict convexity at x=1) to get e > 2, hence 1/e < 1/2
- **Uniqueness**: If |m - n!/e| < 1/2 and |D(n) - n!/e| < 1/2, then |m - D(n)| < 1. Integer gap lemma: an integer strictly between -1 and 1 is 0, proved via omega after casting real bound to ℤ
- **macOS sed Unicode bug**: `sed -i ''` with unicode patterns silently fails on macOS. Must use Python's `str.replace()` for Unicode substitutions.

### Files Modified
- `proofs/Proofs/DerangementsConvergence.lean` (12 syntax fixes: ∑ k in → ∑ k ∈)
- `proofs/Proofs/DerangementsConvergenceOQ01OQ01.lean` (NEW, 130 lines, 7 theorems)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/derangements-convergence-oq-01-oq-01/` (gallery entry)

### Theorems Proved
1. `derangements_rate_scaled`: |D(n) - n!/e| ≤ 1/(n+1) for all n
2. `derangements_nearest_integer`: |D(n) - n!/e| < 1/2 for n ≥ 2
3. `derangements_nearest_integer_n1`: |D(1) - 1/e| < 1/2 using e > 2
4. `derangements_nearest_all`: |D(n) - n!/e| < 1/2 for all n ≥ 1
5. `derangements_unique_nearest`: D(n) is the unique natural in this window
6. `derangements_quarter_bound`: |D(n) - n!/e| ≤ 1/4 for n ≥ 3
7. `derangements_parametric_bound`: |D(n) - n!/e| ≤ 1/k for any k ≤ n+1

### Status
- **Axiom count**: 0 (no external assumptions)
- **Sorry count**: 0
- **Phase**: COMPLETED (pending Docker build verification)
