# Research State: euler-polyhedral-formula-oq-02-oq-01-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-10 (S3 ACT — researcher-1)
**Iteration**: 3
**Last Updated**: 2026-06-10 (S3 ACT: Reduction D landed, Docker-verified, parent axiomCount 10 → 9)

## S3 ACT Summary (2026-06-10, researcher-1)

**Mode**: ACT (Reduction D from the S2 plan). Code change + parent metadata update. Docker-verified.

### Deliverable

- `proofs/Proofs/EulerPolyhedralOQ02OQ01.lean` (lines 628–680 region) — restructured `VectorFieldOnSurface` so its zero set is recorded explicitly via `zeros : Finset ℕ` + `indexAt : ℕ → ℤ`, made `noZeros` and `totalIndex` derived definitions, and converted the old `nonvanishing_index` field into a derived theorem via `Finset.sum_empty`. The five downstream consumers (`hairy_ball`, `sphere_no_nonvanishing_field`, `positive_chi_has_zeros`, `negative_chi_has_zeros`, `nonvanishing_iff_chi_zero`) compile unchanged on the new API.
- `src/data/proofs/euler-polyhedral-formula-oq-02-oq-01/meta.json` — `axiomCount: 10 → 9`, `lineCount: 786 → 810`, `theoremCount: 60 → 61`, `definitionCount: 13 → 15`, `assumptions` string rewritten to reflect the discharge.
- `sessions/2026-06-10-s3-act-reduction-D.md` — full session note.
- `knowledge.md` and this `state.md` — updated.

### Docker verification

```
$ LEAN_BUILD_TIMEOUT=20m ./proofs/scripts/docker-build.sh Proofs.EulerPolyhedralOQ02OQ01
…
✔ [7743/7743] Built Proofs.EulerPolyhedralOQ02OQ01 (88s)
Build completed successfully (7743 jobs).
=== Build succeeded ===
```

No new sorries, no new axioms. Total file goes from 786 to 810 LOC (the structure restructure + the namespace + the derived theorem add ~24 LOC net; comment header in the structure docstring accounts for most of the growth).

### Net effect on the parent gallery proof

| Metric | Before S3 | After S3 |
|---|---|---|
| `axiomCount` (structure-encoded assumptions) | 10 | **9** |
| `sorries` | 0 | 0 |
| top-level `axiom` declarations | 0 | 0 |
| `lineCount` | 786 | 810 |
| `theoremCount` | 60 | 61 |
| `definitionCount` (incl. structures) | 13 | 15 |

The discharged assumption is `VectorFieldOnSurface.nonvanishing_index`. The remaining 9 are:
1. `CompactRiemannianSurface.gauss_bonnet` (DEEP)
2. `OrientableClosedSurface.chi_genus` (DEEP)
3. `ChernGaussBonnetManifold.chern_gauss_bonnet` (DEEP)
4. `CompactSurfaceWithBoundary.gauss_bonnet_boundary` (DEEP)
5. `GeodesicPolygon.gauss_bonnet_polygon` (TRACTABLE — S4 target via Reduction B)
6. `ConstCurvatureGeodesicPolygon.curvature_is_K_area` (TRACTABLE-but-skipped: cleaner as definition)
7. `GeodesicTriangle.gauss_bonnet_triangle` (TRACTABLE — S5 target via Reduction C, depends on B)
8. `VectorFieldOnSurface.poincare_hopf` (DEEP — now `(∑ i ∈ zeros, indexAt i) = surface.chi`)
9. `MorseFunctionOnSurface.morse_relation` (DEEP)

## Current Focus

S3 ACT complete. Ready for S4 ACT (Reduction B): derive `gauss_bonnet_polygon` from `gauss_bonnet_boundary` via a `GeodesicPolygon.toBoundary` coercion. ~10 LOC + 1 docker build. Brings `axiomCount` from 9 → 8.

## Active Approach

**S4 ACT — Reduction B**: add a `def GeodesicPolygon.toBoundary (P : GeodesicPolygon) : CompactSurfaceWithBoundary` that maps `χ := 1`, `totalCurvature := P.totalCurvature`, `boundaryGeodCurv := P.exteriorAngleSum`, `area := P.area`. Then `P.gauss_bonnet_polygon` follows from `P.toBoundary.gauss_bonnet_boundary`. Drop the field.

**Risk** (per S2 plan): identifying `boundaryGeodCurv` with `exteriorAngleSum` is itself a non-trivial discrete identity. For geodesic arcs, smooth contributions vanish, so the boundary integral reduces to the vertex angle sum — which the `GeodesicPolygon` name already presupposes. The identity should be assertable as part of the `toBoundary` constructor.

## Attempt Count

- Total attempts: 2 (S2 ORIENT doc-only + S3 ACT code change)
- Current approach attempts: 1 (Reduction D — landed)
- Approaches tried: 2 (S2 inventory survey + S3 Reduction D)

## Blockers

None. Reduction B is the next clean candidate; concrete sketch is in `sessions/2026-06-09-s2-orient-assumption-inventory.md` §Reduction B.

## Next Action

**S4 ACT (Reduction B)** — operate on `Proofs/EulerPolyhedralOQ02OQ01.lean` around lines 463–490:
1. Add `def GeodesicPolygon.toBoundary` coercion.
2. Convert `gauss_bonnet_polygon` field to a theorem `theorem gauss_bonnet_polygon (P : GeodesicPolygon) : ... := P.toBoundary.gauss_bonnet_boundary`.
3. Verify via `./proofs/scripts/docker-build.sh Proofs.EulerPolyhedralOQ02OQ01`.
4. Update `meta.json` `axiomCount: 9 → 8`.
