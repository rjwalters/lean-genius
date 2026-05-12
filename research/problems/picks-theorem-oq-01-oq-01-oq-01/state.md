# Current State

**Phase**: PLAN
**Since**: 2026-05-12T11:30:00Z
**Iteration**: 4
**Last researcher**: researcher-4 (S3-prep — primitive case `twiceArea = 1 ⇒ I = 0`)
**Most recent PR**: research(picks-theorem-oq-01-oq-01-oq-01): S3-prep — general primitive base case via partition-sum identity

## Current Focus

Bridge `PicksTheoremOQ01OQ01` (primitive triangulation, 0 axioms, verified)
and `PicksTheoremOQ02` (GCD boundary count, 0 axioms, verified) into a
constructive Pick's theorem for lattice triangles.

## Active Approach

**S1 OBSERVE — bridge scaffold (prior session).**
**S2 OBSERVE — real strictly-interior lattice-point count (prior session).**
**S3-prep — primitive case `twiceArea = 1 ⇒ realInteriorCount = 0` (this session).**

`Proofs/PicksTheoremOQ01OQ01OQ01.lean` adds three new theorems (502 lines
total, 0 sorries, 0 axioms):

12. `cross2_partition_sum (T : LatticeTriangle) (p : ℤ × ℤ) :
    cross2 T.v1 T.v2 p + cross2 T.v2 T.v3 p + cross2 T.v3 T.v1 p = T.det`
    — the partition-sum identity, proved by `unfold; ring`.
13. `primitive_no_strict_interior (T : LatticeTriangle)
    (h : T.twiceArea = 1) (p : ℤ × ℤ) : ¬ T.StrictInterior p` — the core
    impossibility lemma, proved by `omega` after combining the
    partition-sum identity with the constraint `|T.det| = T.twiceArea = 1`.
14. `primitive_realInteriorCount_zero (T : LatticeTriangle)
    (h : T.twiceArea = 1) : T.realInteriorCount = 0` — the **general
    primitive base case** of Pick's induction, holding for *every*
    primitive lattice triangle (not just the unit instance verified
    by `native_decide` in S2).

The proof avoids bounding-box enumeration: the three cross-products
sum to `T.det = ±1`, so if all three had the same strict sign each
would be `≥ 1` in absolute value, forcing the sum to have absolute
value `≥ 3` — a contradiction. The `StrictInterior` predicate fails
*everywhere*, not just inside the bounding box.

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

**S3-full — Additivity for primitive gluing.**

With the primitive base case now closed in full generality
(`primitive_realInteriorCount_zero`), the remaining S3 work is the
additivity step: when two lattice triangles `T₁`, `T₂` share an edge
`e` with `gcd(e) = 1` (no interior boundary lattice points), the real
interior counts satisfy

  `realInteriorCount (T₁ ∪ T₂) = realInteriorCount T₁
                                   + realInteriorCount T₂
                                   + (boundary points strictly on e)`.

The same identity holds for `pickInterior` by `pick_formula_cleared`.
Combining with `primitive_realInteriorCount_zero` and
`PicksTheoremOQ01OQ01.exists_primitive_triangulation` (S4) then closes
the full Pick induction.

Estimated effort for S3-full: 200–400 lines.  Possible decomposition:

1. Define `LatticeTriangle.union (T₁ T₂ : LatticeTriangle) : LatticeTriangle`
   (or work with the multiset of two triangles, depending on the
   convexity setup).
2. Prove `realInteriorCount_union_of_shared_edge_gcd_one`.
3. Prove the matching `pickInterior_union` identity using
   `pick_formula_cleared` and `boundaryCount_union_of_shared_edge_gcd_one`.

Each step is self-contained and could be pursued in a separate iteration.

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 3
- Approaches tried: 1 (bridge-via-cleared-form + primitive-base-case)
