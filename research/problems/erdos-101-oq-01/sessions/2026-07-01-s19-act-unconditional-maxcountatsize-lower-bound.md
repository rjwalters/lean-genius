# S19 — ACT: first unconditional positive lower bound on the extremal function

**Date**: 2026-07-01
**Agent**: researcher-1
**Mode**: ACT (edits `Erdos101OQ01.lean` + gallery `meta.json`)

## Context

Erdős #101 OQ-01 is a saturated formalization (S1–S18). The two remaining
`sorry`s are genuinely open mathematics:

1. `erdos_101_oq_01` — the $100 *four-point lines are o(n²)* conjecture.
2. `solymosi_stojakovic_lower_bound` — the Ω(n^{2−C/√log n}) 2013 construction
   (algebraic geometry over 𝔽_q, deferred).

The extremal function `maxCountAtSize n := sSup {fourPointLineCount Q | |Q|=n,
NoFiveCollinear Q}` had an unconditional `O(n²)` **upper** bound
(`maxCountAtSize_le_maxFourPointLines`), but every **lower** bound on it
(`maxCountAtSize_not_O_rpow` and the refutations behind it) was carried by the
deferred `solymosi_stojakovic_lower_bound` `sorry`. S18 proved
`exists_noFiveCollinear_fourPointLineCount_pos` (a no-five-collinear set with a
genuine four-point line) but never transferred that positivity to
`maxCountAtSize`. So the extremal function had **no `sorry`-free positive lower
bound at any size**.

## What this session adds

One theorem in `Erdos101OQ01.lean`:

- `one_le_maxCountAtSize_four : 1 ≤ maxCountAtSize 4`.

Proof (sorry-free, axiom-free): the `x`-axis quadruple
`{(0,0),(1,0),(2,0),(3,0)}` has exactly four points, so it is no-five-collinear
by `noFiveCollinear_small` (vacuously); it is a single four-point line, so
`fourPointLineCount_ge_of_family` (the S18 tool) gives
`1 ≤ fourPointLineCount P`; and `le_maxCountAtSize P` lifts that count to the
supremum `maxCountAtSize P.points.card = maxCountAtSize 4`.

This is the file's first **unconditional** positive lower bound on the extremal
function itself — not merely on `fourPointLineCount` of a fixed set. Combined
with `maxCountAtSize_le_maxFourPointLines` it pins `maxCountAtSize` between an
unconditional constant lower bound and the elementary quadratic upper bound, so
the OQ-01 gap now has both sides witnessed without appeal to the deferred
Solymosi–Stojaković construction.

## Counters

| Metric | Pre-S19 | Post-S19 |
|---|---|---|
| Sorries | 2 | 2 (unchanged; the two OPEN ones) |
| Axioms | 0 | 0 |
| Theorems | 24 | 25 (+1) |
| Lemmas | 1 | 1 |
| Defs | 7 | 7 |
| LOC | 987 | 1066 |

## Build verification

Verified via direct `env -u LAKE lake env lean Proofs/Erdos101OQ01.lean` against
the host Mathlib oleans (v4.26.0) + a freshly built `Erdos101Problem.olean`:
clean typecheck, only the two expected `sorry` warnings at lines 113
(`erdos_101_oq_01`) and 588 (`solymosi_stojakovic_lower_bound`). The Docker
wrapper was unusable this session (5 concurrent `lean-build` containers were
actively rebuilding the shared `.lake`, transiently removing aesop oleans — the
concurrent-`.lake`-race SIGBUS pattern); the single-file `lake env lean` path is
the ground-truth verification, matching S14's precedent.

## Next-action candidates

1. **Positivity at every size `n ≥ 4`** (upgrade this size-4 fact to all sizes).
   Clean construction: the `x`-axis quadruple `A = {(0,0),…,(3,0)}` together with
   a parabola tail `B = {(k, k²) : 1 ≤ k ≤ n−4}`. No-five-collinear proof:
   parabola points are pairwise-triple non-collinear (`(b−a)(c−a)(c−b) ≠ 0`
   algebra), and any line through ≥3 of `A` is the `x`-axis, which misses `B`
   (all `y = k² ≥ 1 > 0`); so among 5 collinear points either ≥3 lie in `B`
   (contradiction) or ≥3 lie in `A` (forcing the `x`-axis, on which no `B` point
   sits). Estimated ~120–150 LOC; the membership casework over the 4-element `A`
   is the main burden.
2. **Cauchy–Schwarz refinement** of `fourCollinearThrough_bound ≤ (n−1)/3` for a
   `1 − o(1)` leading constant on the `n²/12` upper bound (still Θ(n²)).
3. **Deferred (OPEN)**: `erdos_101_oq_01` ($100 prize) and
   `solymosi_stojakovic_lower_bound` (finite-field construction).
