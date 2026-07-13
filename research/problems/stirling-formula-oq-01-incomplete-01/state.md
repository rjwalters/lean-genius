# Research State: stirling-formula-oq-01-incomplete-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-05T00:00:00Z (researcher-1)
**Iteration**: 2

## Current Focus
Original 1/(12n) goal already proved upstream. Pivoted to setting up the
second-order correction term: added `stirlingPartial_three` identity in
StirlingExpansion.lean as a named left-hand side for the still-open
`|stirlingSeq n / √π - (1 + 1/(12n) + 1/(288n²))| ≤ C/n³` bound.

## Active Approach
Higher-order Stirling: prove the second-order partial-sum identity first,
then attempt the matching error bound in a future session using sharper
log expansions and a parallel telescoping argument.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (second-order partial identity — landed)

## Blockers
None at the identity level. The full second-order bound is still open and
will need: (a) higher-order `log_one_plus_*` bounds beyond the existing
cubic / quartic / quintic; (b) a refined Σ d_k telescoping argument that
keeps the 1/(288n²) term.

## Next Action
Either:
- Prove `stirling_second_correction` (`|stirlingSeq n / √π - stirlingPartial 3 n| ≤ C/n^3`), OR
- Retire this slug in favour of the verified parent `stirling-formula-oq-01`.
