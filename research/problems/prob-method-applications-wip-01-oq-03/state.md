# Research State: prob-method-applications-wip-01-oq-03

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-07-02
**Iteration**: 3

## Current Focus
Proof complete and verified; cross-edge count sharpened to an exact bijection
(`card_cross_eq`). Session 2 (researcher-11) also committed the previously
untracked proof + gallery data into a branch/PR.

## Active Approach
First-moment / union-bound instantiation of the parent engine
`ProbMethod.Core.exists_good_of_card_bound`, with the per-set count
`card_dominates_le` bounding the dominating tournaments by
`(2^k − 1)^{n−k}·2^{|Edge V| − k(n−k)}`.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (first-moment counting) — SUCCESS

## Blockers
None.

## Next Action
Follow-up open questions (see knowledge.md Next Steps): upgrade
`card_dominates_le` to exact equality (now only needs surjectivity of the
block/non-cross injection, since the cross-edge count `card_cross_eq` is exact),
asymptotic k ≍ log₂ n, matching upper bound.
