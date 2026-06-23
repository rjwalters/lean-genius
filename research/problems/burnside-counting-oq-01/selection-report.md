# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 397 in pool (6 truly available, 391 graduated/stale)

## Selected Problem

- **ID**: burnside-counting-oq-01
- **Name**: Burnside Counting — Prove rotatedIndex_add Composition Law
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 5/10
- **Knowledge Score**: ~2 items (WEAK) — initial knowledge collected
- **Composite Score**: 56 (tied for top among EMPTY/WEAK knowledge problems)
- **Status**: available

## Selection Rationale

1. **Pool context**: After removing graduated/completed problems, only 6 truly available problems remain in the seeker worktree. `burnside-counting-oq-01` is among the top 3 tied at composite score 56.
2. **Domain diversity**: Combinatorics/group theory (Burnside's lemma, necklace counting) is underrepresented in recent selections which focused on discrete geometry, additive number theory, and Erdős problems.
3. **Concrete and tractable**: The goal is a specific modular arithmetic composition law — `omega` or ring-theoretic tactics may close this quickly.
4. **No workspace**: Needs full initialization (not yet in research problems directory on feature/seeker branch).
5. **Quality gate passed**: Not a mathematical open conjecture. Specific formalization target. Not a near-duplicate of recent selections.

## Rejection Summary

- **erdos-871**: WEAK knowledge (32 lines, ~6 items) → score -1923 after tier penalty
- **birthday-problem-oq-02-oq-01-oq-01**: WEAK knowledge (21 lines) → score -925; also started today (very new)
- **abel-ruffini-galois-extensions-oq-02**: WEAK knowledge → score -943
- **abel-ruffini-galois-extensions-oq-01**: Tied at 56 but Abel-Ruffini/Galois domain recently covered
- **binary-gcd-oq-01-oq-01**: Tied at 56, similar algorithmic number theory domain to recent selections
- **cevas-theorem-oq-01**: REJECTED — already graduated (Feb 15, 2026), pool status stale
- **e-transcendental-oq-01-oq-01**: REJECTED — "Is e+π irrational?" is an open mathematical problem (moonshot)
- **Confidence**: medium-low (pool is mostly stale; need pool refresh for better candidates)

## Pool Health Assessment

The seeker worktree pool shows 397 available but 391 are actually graduated/completed — pool is critically stale. True available count: 6.

**Immediate action needed**: The PR #10164 (adding 11 new problems to main repo pool) addresses replenishment for the main pipeline. The seeker worktree pool needs its own refresh.

## Related Gallery Proofs

- `burnside-counting`: Parent proof — Burnside's Lemma and Necklace Counting
- `orbit-stabilizer`: Related group action theory

## Suggested First Steps

1. Read `src/data/proofs/burnside-counting/` to locate the `rotatedIndex` definition
2. Find where the composition law is used/axiomatized in the Lean source
3. Try `omega` after `simp [rotatedIndex]` to close the modular arithmetic goal
4. If `omega` fails, use `Nat.add_mod` and `Nat.sub_mod` lemmas explicitly

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available (pool) | 397 |
| Truly available (non-graduated) | 6 |
| In Progress | 9 |
| Completed/Graduated (pool) | 260 |
| **Graduated (registry)** | **1236** |

## Candidate Pool Health

- Pool depth: **CRITICAL** — pool shows 397 available but 391 are stale (graduated)
- True available: only 6 problems
- Recommendation: Run pool sync from registry; replenish with new gallery problems
- Note: PR #10164 adds 11 new problems to main repo pipeline
