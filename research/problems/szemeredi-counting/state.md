# Research State: szemeredi-counting

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-03-22
**Iteration**: 2

## Current Focus
Proving `bad_vertices_small` — the key lemma connecting neighborhoods to regularity.

## Active Approach
Contradiction: if |bad| ≥ ε|A|, regularity gives d(bad,B) ≥ d-ε, but all bad vertices have small neighborhoods so d(bad,B) < d-ε. Most of proof complete.

## Attempt Count
- Total attempts: 2
- Current approach attempts: 2
- Approaches tried: 1

## Blockers
`edge_count_eq_sum_neighborhoods` — fiber decomposition of product filter. Standard combinatorial identity but Lean API is non-trivial.

## Next Action
1. Prove edge_count_eq_sum_neighborhoods via Finset.cons_induction
2. Use it to close hd_lt inside bad_vertices_small
3. Then prove counting_lemma via iterated bad vertex elimination
