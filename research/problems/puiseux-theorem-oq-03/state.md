# Research State: puiseux-theorem-oq-03

## Current State
**Phase**: BLOCKED (combinatorially complete; analytic bridge blocked)
**Path**: full
**Since**: 2026-06-28T13:30:00-07:00
**Iteration**: 6

## Current Focus
Combinatorial Newton-polygon theorem is fully formalized (1081L, 53 thm,
0 sorries / 0 axioms; all three invariants — sorted slopes, widths-sum,
slope×width drop — on the concrete `exists_lowerHull` chain). Remaining open
core is the analytic bridge (polygon slopes/widths ↔ valuations/multiplicities
of roots of `P ∈ K⸨x⸩[Y]`).

## Active Approach
None active — blocked on missing Mathlib infrastructure (see Blockers).

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
**Analytic bridge needs a valued Puiseux field, absent from Mathlib.**
- PRESENT (drifted cache, new since 4.26.0): `Valued.v : Valuation K⸨X⸩ ℤᵐ⁰`
  (`Mathlib/RingTheory/LaurentSeries.lean`) + monomial API. Base field `K⸨x⸩`
  is now a valued field upstream.
- ABSENT: `PuiseuxSeries` / `HahnSeries ℚ K` and a ℚ-valued (rational-exponent)
  valuation. Polygon slopes are ℚ-valued (roots live in ramified `K⸨x^{1/n}⸩`);
  the available valuation is ℤᵐ⁰-valued on the unramified base, so the
  correspondence `edgeSlope = −v(root)` is not even statable.
- Building the valued Puiseux field is foundational >1000-line infra (BLOCKED
  category). See `sessions/2026-06-28-s05-valuation-api-drift-blocker-refine.md`.

## Next Action
If revisited: construct the valued Puiseux field (`PuiseuxSeries K` + ℚ-valuation
+ ramified embedding of `K⸨x⸩`) as a separate large infrastructure PR — the polygon
(combinatorial) side is already complete. Do NOT add further combinatorial lemmas;
that is cosmetic on a finished API.
