# Knowledge: taylor-sincos-convergence-oq-03-wip-01

## Summary

No research sessions yet. Problem initialized by Seeker on 2026-04-05.

## Key Facts

- Source file: `proofs/Proofs/TaylorSinCosConvergenceOQ03.lean`
- 3 sorries: `alternating_tail_bound`, `sin_alternating_remainder`, `cos_alternating_remainder`
- The key sorry is `alternating_tail_bound` — the other two follow from it
- `sinTermAbs_antitone` already proved for `|x| ≤ 1` — may need extension for general x
- Mathlib has `Mathlib.Topology.Algebra.InfiniteSum.Alternating` — check this first

## Open Questions

1. Does Mathlib's `InfiniteSum.Alternating` have a direct `alternating_tail_bound`-style theorem?
2. Is `sinTermAbs_antitone` provable for all x (not just |x| ≤ 1), or is the general bound via eventual antitone?
3. How does `Real.hasSum_sin` connect to the tail-sum expression in `sin_alternating_remainder`?
