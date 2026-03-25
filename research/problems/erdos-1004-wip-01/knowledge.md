# Erdős #1004: Distinct Consecutive Totient Values

## Problem Summary

For c > 0, if x is sufficiently large, does there exist n ≤ x such that
φ(n+1), φ(n+2), ..., φ(n+⌊(log x)^c⌋) are all distinct?

**Status**: OPEN (partial results from EPS 1987)
**File**: `proofs/Proofs/Erdos1004Problem.lean`
**Sorries**: 2 remaining (was 3, then 5 originally)
**Axioms**: 3 (EPS87 bound)

## Session 2026-03-25 (Session 2) - Prove run_length_sublinear

**Mode**: FRESH (REVISIT of in-progress problem)
**Outcome**: progress (1 sorry eliminated)

### What I Did
- Proved `run_length_sublinear`: maxDistinctRunLength(n)/n → 0 as n → ∞
  - Created helper `maxDistinctRunLength_le_eps87` bounding sSup via EPS87 axiom
  - Used squeeze theorem with bound g(n) = 1/exp(c·(log n)^{1/3})
  - Proved limit via composition chain: log→∞, rpow→∞, c*·→∞, exp→∞, inv→0
- Fixed pre-existing `Nat.dvd_sub'` build error in `totient_eq_two_iff`
  - Used Euclidean algorithm approach: gcd_rec + manual mod proof via nth_rewrite
- Assessed `longer_runs_need_larger_n`: too deep for this session (requires existence of K-long distinct totient runs for arbitrary K)

### Key Findings
- The sSup bound technique: csSup_le + Nat.le_floor + Nat.floor_le cleanly transfers real bounds to ℕ sup
- rpow cube root identity: `(a^3)^(1/3) = a` via rpow_natCast + rpow_mul + norm_num
- omega cannot handle `n % (n-1) = 1` for variable n; need manual Euclidean approach
- `longer_runs_need_larger_n` reduces to existence of a single m with K distinct consecutive totients (via ∃ n₀ trick), but even that single existence is deep

### Files Modified
- `proofs/Proofs/Erdos1004Problem.lean` (424 → 492 lines, 3 → 2 sorries)
- `src/data/proofs/erdos-1004/meta.json` (updated counts)
- `src/data/research/problems/erdos-1004-wip-01.json` (updated knowledge)

### Next Steps
- `longer_runs_need_larger_n`: try CRT-based constructive existence or density argument
- `distinct_totients_asymptotic`: deep analytic result (Ford 1998), likely needs Aristotle or axiomatization
- Consider submitting both as HARD to Aristotle
