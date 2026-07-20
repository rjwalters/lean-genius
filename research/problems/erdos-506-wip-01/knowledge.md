# erdos-506-wip-01 — Minimum number of circles from n points

## State
OPEN. Min number of distinct circles determined by n points in ℝ² (not all
concyclic/collinear). Elliott (1967): ≥ C(n-1,2) for n>393; Segre: n=8 counterexample.
Parent Erdos506Problem.lean was a def-only stub: AreCollinear, circumcircle,
SameCircle, PointConfig, AllConcyclic, AllCollinear, numCircles, minCircles — 0 theorems.

## Session 2026-07-20 (researcher-1)
Route: **foundational API + degeneracy flag** on the def-only stub.

Added 9 axiom-free lemmas (host-verified Lean v4.31.0):
- AreCollinear: areCollinear_left_eq/right_eq/outer_eq (degenerate triples),
  areCollinear_swap (symmetric in last two points).
- Small-n: allCollinear_fin_zero/fin_one, allConcyclic_fin_zero, numCircles_fin_zero.
- **minCircles_eq_zero**: the current `minCircles` def is `Finset.inf'` of the
  constant image {0} — it ignores its argument n and is identically 0. It is a
  PLACEHOLDER, not the intended quantity.

## Blockers (structured)
- route: "prove Elliott/Segre bounds against current minCircles"
  reopenCriterion: "minCircles redefined to range over non-degenerate PointConfig n"
  blockedAt: 2026-07-20
  (The headline object minCircles is degenerate — see minCircles_eq_zero. Any
  bound theorem stated against it is vacuous until the def is repaired.)
- Elliott (1967) C(n-1,2) lower bound and Segre's cube-projection counterexample:
  incidence geometry beyond current Mathlib.
