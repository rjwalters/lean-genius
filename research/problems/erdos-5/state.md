# Current State

**Phase**: ACT (extension)
**Since**: 2026-05-08T11:00:00Z
**Iteration**: 2

## Current Focus

Forward density direction and unconditional oscillation lemmas added to
`Erdos5PrimeGaps.lean`. The key contribution is the iff characterization
`erdos_5_iff_dense_at_every_point` which shows that Erdős #5 is
equivalent to a purely distributional density statement about the
normalizedGap sequence.

## Active Approach

Strengthen the existing reduction `erdos_5_from_dense_values` (one
direction) into an iff by proving the forward direction
`frequently_near_of_isLimitPoint` — any subsequence convergent to C
injects ℕ (via `f ∘ (· + K)`) into the ε-ball around C, hence the set
of n with normalizedGap n near C is infinite.

## Blockers

None — the open conjecture itself remains, but the structural theory
is more complete.

## Next Action

Optional follow-ups:
- A `MapClusterPt`-based reformulation connecting `IsLimitPoint` to
  Mathlib's filter cluster point machinery.
- A `Filter.limsup`/`Filter.liminf` formulation in `EReal`:
  `liminf normalizedGap atTop = 0` and `limsup normalizedGap atTop = ⊤`.
- Investigate whether Hildebrand–Maier follows from a weaker
  hypothesis (e.g. Westzynthius + an Erdős–Ricci style measure argument).

## Attempt Counts

- Total attempts: 5
- Current approach attempts: 2
- Approaches tried: 2
