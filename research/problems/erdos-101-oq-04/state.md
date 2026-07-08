# Current State

**Phase**: ACT
**Since**: 2026-07-08T00:00:00Z
**Iteration**: 2

## Current Focus

Reusable counting infrastructure for lower-bound witnesses.

## Active Approach

Path B (explicit constructions). This iteration factored out the counting
engine shared by every witness (`crossSet`, `asteriskSet`, `gridSet`): the
`subset-of-filter → Finset.card_le_card` argument that turns a family of
certified four-point collinear quadruples into a lower bound on
`fourPointLineCount`.

## Progress This Iteration (VERIFIED, 0-axiom)

Added two general lemmas to `Proofs/Erdos101OQ04.lean` (build-verified,
3062 jobs, only the two pre-existing OPEN sorries remain):

- `fourPointLineCount_ge_of_subset` — set form: any `Finset` `T` of
  four-point collinear subsets of `P.points` gives `T.card ≤
  fourPointLineCount P`.
- `fourPointLineCount_ge_of_injOn_family` — indexed form: an injective
  family `L : Fin k → Finset (ℝ×ℝ)` of four-point collinear subsets gives
  `k ≤ fourPointLineCount P` (the natural shape a growing construction
  produces — one line per index).

These separate the *easy* counting from the *hard* geometry that is the
genuine open content, so future construction PRs supply only the collinear
quadruples and their distinctness/injectivity.

## Blockers

The two OPEN construction sorries are unchanged and remain the frontier:
- `grunbaum_lower_bound_three_halves` (Ω(n^{3/2}))
- `solymosi_stojakovic_lower_bound` (n^{2−o(1)})
A general-n growing witness still needs a clean "no five collinear" proof
(ruling out accidental cross-gadget alignments for all n) — grids alone
cap at 10 four-point lines under the no-five-collinear constraint.

## Next Action

Build a concrete growing family and discharge `k ≤ fourPointLineCount`
through `fourPointLineCount_ge_of_injOn_family`; the remaining work is the
per-family no-five-collinear certificate.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
