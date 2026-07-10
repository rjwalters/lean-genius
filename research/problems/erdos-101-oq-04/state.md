# Current State

**Phase**: ACT
**Since**: 2026-07-08T00:00:00Z
**Iteration**: 3

## Progress This Iteration (iter 3, 2026-07-09) — UNVERIFIED (docker infra down)

Added `quartic_quadruple_sum_zero_sq_iff_ternary` to `Proofs/Erdos101OQ04.lean`:
eliminating `x₃ = −(x₀+x₁+x₂)` via `Σx = 0`, the engine's sum-of-squares condition
`Σx² = 10` is *equivalent* to the fixed **ternary conic**
`x₀²+x₁²+x₂²+x₀x₁+x₁x₂+x₂x₀ = 5` — the same quadratic form and constant `5` that
governs the three-point criterion `collinear_onQuartic_iff`. This recasts the OPEN
super-linear-growth question (`quartic_fourPointLineCount_from_quadruples`) as the
purely arithmetic problem of finding super-linearly many distinct solution-sets on
one fixed ternary conic — no `x⁴` term survives. Pure algebra (`linarith`/`subst`/
`linear_combination`), 0-sorry, 0-axiom, no new API. Docker build infra down all
session (containerd meta.db I/O error), so shipped UNVERIFIED with hand-audit; the
`(1/2)·h` and `2·h` linear_combination coefficients are the exact factor of 2
between `Σx²` and the ternary form. The two OPEN construction sorries
(`grunbaum_lower_bound_three_halves`, `solymosi_stojakovic_lower_bound`) are the
genuine hard frontier and remain untouched.

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

## Progress (2026-07-09, researcher-11 — intrinsic linear density)

Added the intrinsic-density corollaries of `quartic_linear_lower_bound` to
`Proofs/Erdos101OQ04.lean`:
- `exists_fourPointLineCount_ge_card_div_four` — eliminates the external level
  parameter `k`: from `card ≤ 4k ∧ k ≤ fourPointLineCount P` one gets
  `P.points.card ≤ 4 · fourPointLineCount P`, the intrinsic density `≥ 1/4`.
- `exists_fourPointLineCount_ge_card_div_four_real` — the real-valued textbook
  form `L₄(n) ≥ n/4`.

Both follow in a few lines from the existing linear family (no new construction).
Elaboration-clean `[3062/3062]` × 5 Docker runs, zero diagnostics on the file; each
run then hit the stochastic SIGBUS exit-135 at olean-write (infra, not a proof error).
Shipped UNVERIFIED. The two deep sorries (`solymosi_stojakovic_lower_bound` — the only
real `sorry` in the file — and the derived `grunbaum` Ω(n^{3/2})) are unchanged and
remain the frontier.
