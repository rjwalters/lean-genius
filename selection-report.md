# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 21 available, 327 in-progress, 1217 completed, 1 graduated

## Selected Problem

- **ID**: birthday-problem-oq-03-oq-01-oq-01-oq-03
- **Name**: Remove the threshold axioms: use a Lean big-integer library to verify birthdayCount3 88 365 vs 365^88 by native_decide
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Composite Score**: 76
- **Status**: available

## Selection Rationale

1. **Highest tractable EMPTY problem after skipping same-session selections**: The algorithm ranked minkowski-theorem-oq-02-oq-01 (composite=78) and bezout-identity-oq-04-oq-01-oq-03 (composite=77) higher, but both were selected in the current seeker session today (4 and 3 commits ago respectively) with workspaces already initialized. Re-selecting them provides no new signal to Researchers. birthday-problem-oq-03-oq-01-oq-01-oq-03 (composite=76) is the highest-scoring fresh selection.

2. **EMPTY knowledge tier**: No research has been done on this specific sub-problem. Immediate exploration value.

3. **High tractability (7/10)**: The approach is concrete — replace two `axiom` declarations with `theorem ... := by native_decide`. The parent proof (2-way birthday problem) already uses native_decide for 146-digit numbers, proving the infrastructure works. The 3-way recurrence has O(n²) ≈ 7744 evaluations.

4. **Domain diversity**: Probability/combinatorics — different from recent selections (analysis, combinatorics/Erdős, algebra).

## Rejection Summary

- **Candidates considered**: 21 available
- **minkowski-theorem-oq-02-oq-01** (composite=78): Skipped — selected in current session (4 commits ago), workspace already initialized, no new signal
- **bezout-identity-oq-04-oq-01-oq-03** (composite=77): Skipped — selected in current session (3 commits ago), workspace already initialized
- **binary-gcd-oq-01-oq-04-oq-01** (sig=5): Below significance threshold relative to alternatives
- **hilbert-10-oq-03** (tract=4): Lower tractability; characterizing number fields with decidable H10 is open research
- All other candidates ranked lower on composite score
- **Confidence**: medium (tight score spread between top EMPTY candidates: 78/77/76/68/68)

## Related Gallery Proofs

- `birthday-problem`: Parent 2-way case — fully verified (0 axioms), uses native_decide for 146-digit integers; direct methodology blueprint
- `birthday-problem-oq-03`: Parent 3-way threshold problem entry
- `birthday-problem-oq-03-oq-01-oq-01`: Direct parent (2 axioms, axiomatized) — this problem eliminates those axioms
- `buffons-needle`: Fellow classic probability problem (separate track)

## Suggested First Steps

1. **OBSERVE**: Run Python to compute `birthdayCount3 88 365` and `birthdayCount3 87 365` externally to confirm the inequalities and gauge number size
2. **ORIENT**: Examine `proofs/Proofs/BirthdayProblem.lean` to see how `native_decide` was applied to 146-digit numbers in the 2-way case
3. **DECIDE**: Attempt `theorem birthday_threshold_lower : 2 * birthdayCount3 88 365 < 365 ^ 88 := by native_decide` in a test file; if it compiles, apply to the main file

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 21 |
| In Progress | 327 |
| Completed | 1217 |
| Graduated | 1 |
| **Total** | **1566** |

## Candidate Pool Health

- **Pool depth**: adequate (21 available)
- **Recommendation**: Pool healthy; no immediate refresh needed
- **Next refresh recommended**: when available drops below 5
