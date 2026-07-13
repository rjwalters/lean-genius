# Current State

**Phase**: ACT (extension)
**Since**: 2026-06-09T02:00:00Z
**Iteration**: 3

## Current Focus

Eventually-form liminf/limsup corollaries added to `Erdos5PrimeGaps.lean`.
The unconditional oscillation lemmas
`frequently_normalizedGap_lt`/`frequently_normalizedGap_gt` are now
reformulated as `not_eventually_le_normalizedGap` (no `ε > 0` is an
eventual lower bound) and `not_eventually_normalizedGap_le` (no `M : ℝ`
is an eventual upper bound), together with the packaging
`normalizedGap_oscillates`. Together with `normalizedGap_nonneg`, these
witness `Filter.liminf normalizedGap atTop = 0` and
`Filter.limsup normalizedGap atTop = ⊤` in any complete extension of `ℝ`
(e.g. `EReal`) without dragging the `EReal` machinery itself into the
file.

## Active Approach

The S3 increment is a self-contained packaging on top of S2's
`erdos_5_iff_dense_at_every_point`. No new axioms, no new dependencies,
and the entire addition is closed by `Set.Finite.subset (Set.finite_Iio
N)` + `Filter.eventually_atTop` rewrites.

## Blockers

None — the open conjecture itself remains. The S3 corollaries close the
gap between the existing `Set.Infinite` oscillation lemmas and the
filter `liminf`/`limsup` reading without forcing an explicit `EReal`
coercion of `normalizedGap`.

## Next Action

Optional follow-ups (carrying the S2 list forward, plus an S3 cleanup):

- (S4 clean) A direct `EReal` upgrade: state `Filter.limsup` (resp.
  `Filter.liminf`) of `fun n => (normalizedGap n : EReal)` along `atTop`
  equals `⊤` (resp. `0`) using `not_eventually_normalizedGap_le` /
  `not_eventually_le_normalizedGap` plus the appropriate `EReal`
  characterization lemma.
- (S4 clean) A `MapClusterPt`-based reformulation connecting
  `IsLimitPoint` to Mathlib's filter cluster point machinery, unlocking
  lemmas like `MapClusterPt.isClosed`.
- (S5 substantive) Investigate whether the Hildebrand–Maier axiom
  (∃ arbitrarily large finite limit points) follows from
  Westzynthius + an Erdős–Ricci style measure argument; if so, the
  axiom count drops 3 → 2.

## Attempt Counts

- Total attempts: 6
- Current approach attempts: 1
- Approaches tried: 2
