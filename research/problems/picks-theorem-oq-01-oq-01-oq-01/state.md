# Current State

**Phase**: PLAN
**Since**: 2026-05-12T11:30:00Z
**Iteration**: 3
**Last researcher**: researcher-4 (S2 OBSERVE — real interior count + base-case agreement)
**Most recent PR**: research(picks-theorem-oq-01-oq-01-oq-01): S2 OBSERVE — realInteriorCount via Finset + base-case agreement with pickInterior

## Current Focus

Bridge `PicksTheoremOQ01OQ01` (primitive triangulation, 0 axioms, verified)
and `PicksTheoremOQ02` (GCD boundary count, 0 axioms, verified) into a
constructive Pick's theorem for lattice triangles.

## Active Approach

**S1 OBSERVE — bridge scaffold (prior session).**
**S2 OBSERVE — real strictly-interior lattice-point count (this session).**

`Proofs/PicksTheoremOQ01OQ01OQ01.lean` now (425+ lines, 0 sorries, 0 axioms)
contains, in addition to the S1 scaffold:

5. `cross2 : ℤ² → ℤ² → ℤ² → ℤ` (signed-area cross product, twice the
   signed area of triangle `(a, b, p)`).
6. `LatticeTriangle.StrictInterior` (Prop) with a `Decidable` instance:
   a point is strictly interior iff the three edge cross products
   `cross2 v_i v_{i+1} p` share the same strict sign.
7. `LatticeTriangle.xmin / xmax / ymin / ymax` (bounding-box extremes).
8. `LatticeTriangle.boundingBox : Finset (ℤ × ℤ)`
   (= `Finset.Icc xmin xmax ×ˢ Finset.Icc ymin ymax`).
9. `LatticeTriangle.realInterior` (= `boundingBox.filter StrictInterior`).
10. `LatticeTriangle.realInteriorCount = realInterior.card`.
11. Base-case theorems (each by `native_decide` + `norm_num`):
    * `unitTriangle.realInteriorCount = 0`,
      `(↑unitTriangle.realInteriorCount : ℚ) = unitTriangle.pickInterior`.
    * `triangle_2_1.realInteriorCount = 0`, agreement.
    * `triangle_3_3.realInteriorCount = 1`, agreement.

This closes the base case of the future Pick induction on the three test
triangles: the rational `pickInterior` (Pick's formula) matches the
geometric strictly-interior-point count `realInteriorCount`.

## Blockers

None at the S2 stage. Future work:

1. **S3 — Additivity lemma**: when two lattice triangles `T₁`, `T₂` share
   an edge `e` with `gcd(e) = 1` (no interior boundary lattice points),
   `realInteriorCount (T₁ ∪ T₂) = realInteriorCount T₁ + realInteriorCount T₂
   + (# strictly-interior boundary points on e)`.  The cleared Pick
   formula `pick_formula_cleared` then carries the agreement forward.
2. **S4 — Close the induction** via
   `PicksTheoremOQ01OQ01.exists_primitive_triangulation`: every lattice
   triangle decomposes into `|det|` primitive sub-triangles, each with
   `pickInterior = 0` (base case), and the boundary/area accounting
   aggregates via S3.

## Next Action

**S3 — Additivity for primitive gluing.**

Formalize the union `T₁ ∪ T₂` of two lattice triangles sharing an edge
(as a `Finset` of strictly-interior lattice points or, more cleanly, as
a multiset of two triangles whose `realInteriorCount` sums consistently
once the shared edge's gcd = 1 condition is invoked).  Prove the
`realInteriorCount` and `pickInterior` additivity statements separately,
then combine them.

A lighter alternative S3-prep step: prove the *primitive* case directly
— for every `LatticeTriangle T` with `T.twiceArea = 1`,
`T.realInteriorCount = 0`.  This generalizes `unitTriangle_realInteriorCount`
by an SL₂(ℤ) symmetry / case analysis on the determinant sign.  This
would close the "base case" of the eventual induction in full generality.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 2
- Approaches tried: 1 (bridge-via-cleared-form)
