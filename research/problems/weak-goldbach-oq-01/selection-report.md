# Selection Report: weak-goldbach-oq-01

**Selected**: 2026-04-23
**By**: Seeker (SELECT mode)
**Composite Score**: 28

## Problem

**ID**: weak-goldbach-oq-01
**Title**: Strong Goldbach Conjecture — Every Even n > 2 is Sum of Two Primes
**Tier**: A
**Significance**: 8/10
**Tractability**: 2/10
**Knowledge Score**: 0 (EMPTY)

## Selection Rationale

1. **EMPTY knowledge tier** grants highest priority in the selection algorithm. No research
   has been recorded for this problem.
2. **Significance 8** reflects outstanding mathematical importance: the strong Goldbach
   conjecture has been verified computationally for all n ≤ 4×10¹⁸, and the weak Goldbach
   (every odd > 5 is sum of three primes) was proved by Helfgott (2013). Lean formalization
   of the strong conjecture and partial results is a high-value target.
3. **Tractability 2**: the full conjecture is open. The researcher should produce an
   axiomatized formalization with Lean statement, document Helfgott's weak Goldbach proof
   as a related landmark, and identify available Mathlib infrastructure.

## Rejection Summary

- **Candidates considered**: 34 available in pool (3 with no prior workspace)
- **Candidates rejected**: 31 already had initialized workspaces from prior seeker batches
- **Confidence**: high — one of 3 genuinely new problems

## Related Gallery Proofs

- `twin-primes-special-oq-01`: closely related prime conjecture (being selected simultaneously)
- `prime-number-theorem`: Mathlib density infrastructure
- `waring-problem` (if in gallery): sum-of-k-th-powers analogue

## Suggested First Steps

1. **OBSERVE**: Check Mathlib for `Goldbach` definitions, `Nat.Prime`, additive combinatorics
   infrastructure in `Mathlib.NumberTheory.Goldbach` or similar paths.
2. **ORIENT**: Determine what currently exists in Mathlib for Goldbach-type results. The
   weak Goldbach (Helfgott) may have Lean components worth referencing.
3. **DECIDE/ACT**: Formalize `∀ n : ℕ, n > 2 → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q`
   as an axiom with documentation of computational verification bounds.

## Pool Summary

| Status | Count |
|--------|-------|
| Available | 34 |
| In Progress | 559 |
| Completed | 1403 |
| Graduated | 3 |
| Blocked | 2 |
| **Total** | **2001** |

## Pool Health

Pool depth adequate (34 available). No refresh needed.
