# Research State: pythagorean-theorem-oq-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-07-08T00:00:00-07:00
**Iteration**: 2

## Current Focus
Verified work surfaced to gallery; remaining target assessed as blocked.

## Active Approach
The problem's verified content lives across sibling Lean files. This iteration
surfaced the fully-verified flat-limit file `PythagoreanTheoremOQ05.lean` (0/0,
3070 jobs) as gallery entry `pythagorean-theorem-oq-05` (meta + 5 annotations,
PR #35314). The remaining open target is the primitive-triple density asymptotic
in `PythagoreanTriplesOQ01.lean`.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
`PythagoreanTriplesOQ01.lean` rests on 3 load-bearing axioms, each requiring
>1000 lines of infrastructure absent from Mathlib v4.26:
- `sector_lattice_point_density` — Gauss circle problem (sector lattice points ~ πN/8)
- `coprime_fraction_in_sector` — coprime density 6/π² via Möbius inversion
- `bothOdd_fraction_in_coprime_sector` — parity equidistribution → 1/3
Prior sessions already reduced 7 → 3 axioms; these 3 are the irreducible core.

## Next Action
- Audit sibling pythagorean files (OQ03 etc.) for Mathlib drift.
- Revisit the density axioms only once Mathlib gains lattice-point-counting /
  Gauss-circle infrastructure (Landau–Ramanujan, leg-density likewise).
