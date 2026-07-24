# Research State: euler-polyhedral-formula-oq-02-oq-01-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-24 (S6 ACT — researcher-1)
**Iteration**: 6
**Last Updated**: 2026-07-24 (S6 ACT — Docker restored; Reduction B landed and docker-verified; researcher-1)

## S6 ACT (2026-07-24, researcher-1) — Reduction B landed

Docker is back (v29.6.2), lifting the S4/S5 Docker-transient block. Reduction B
implemented and verified (`./proofs/scripts/docker-build.sh
Proofs.EulerPolyhedralOQ02OQ01` → "Build completed successfully (8576 jobs)").

**Design correction vs the S2 sketch**: the sketched direction — build
`def GeodesicPolygon.toBoundary` *from* the polygon's loose fields — is
circular: constructing a `CompactSurfaceWithBoundary` requires proving its
`gauss_bonnet_boundary` field, which for that mapping is exactly the
`gauss_bonnet_polygon` identity being dropped. The sound direction (mirroring
S3 Reduction D) **embeds** the boundary structure into the polygon:

- `structure GeodesicPolygon` now has fields `n : ℕ`,
  `toBoundary : CompactSurfaceWithBoundary`, `chi_eq_one : toBoundary.chi = 1`.
- `totalCurvature` / `exteriorAngleSum` / `area` are projection defs
  (`exteriorAngleSum := toBoundary.boundaryGeodCurv` — definitional
  identification, justified because geodesic arcs carry zero smooth κ_g).
- `area_pos` and `gauss_bonnet_polygon` are derived theorems; the latter is
  `gauss_bonnet_boundary` at χ = 1 (`rw [chi_eq_one]`, `push_cast`, `linarith`).
- `ConstCurvatureGeodesicPolygon.curvature_is_K_area` restated as
  `toGeodesicPolygon.totalCurvature = K * toGeodesicPolygon.area`; downstream
  `const_curv_polygon_formula` and `interior_angle_sum` compile unchanged.

**Net**: structure-encoded assumptions 9 → 8; lineCount 810 → 838; theoremCount
61 → 63 (+`area_pos`, +derived `gauss_bonnet_polygon`); definitionCount 15 → 18
(+3 projection defs). meta.json counts, assumptions string, and section anchors
(+28 lines after Part XIV) updated in the same commit.

## S5 GATE-SYNC (2026-06-14, researcher-1)

The S4 BLOCKED flag lived in state.md only: the research JSON read
`status: "active"` / `phase: "ACT"` and `.lean/state/candidate-pool.json`
read `"in-progress"`, so `claim-random` kept re-serving this RICH slug.
Aligned both gates to BLOCKED (JSON `status`/`phase`/`currentState.phase`
→ `blocked`/`BLOCKED`; pool → `"blocked"`, terminal). Docker-transient block —
only Docker-gated work remains (meta.json already verified in-sync at S4).
Un-block by reverting these gates when a build/verify route returns. No
metadata/Lean change.

## S4 BLOCKED (2026-06-13, researcher-1)

**Mode**: triage during the Docker verification blackout. No code change.

The sole remaining work on this slug is **S4 ACT (Reduction B)** — adding a
`GeodesicPolygon.toBoundary` coercion to discharge the `gauss_bonnet_polygon`
structure-encoded assumption (axiomCount 9 → 8). That change is a ~10 LOC code
edit whose only acceptance gate is a successful
`./proofs/scripts/docker-build.sh Proofs.EulerPolyhedralOQ02OQ01`. The Docker
daemon is unresponsive (`docker info`/`docker ps` time out), so the build cannot
run and the reduction cannot be verified. Per project policy, build-dependent
ACT must not be blind-shipped.

**Build-free diligence performed this session (all clean):**
- `src/data/proofs/euler-polyhedral-formula-oq-02-oq-01/meta.json` is fully in
  sync with `proofs/Proofs/EulerPolyhedralOQ02OQ01.lean` on origin/main:
  lineCount 810 == 810, theoremCount 61 == 61 (col-0 `theorem|lemma`),
  definitionCount 15 == 15 (col-0 `def|structure|abbrev|instance`), sorries
  0 == 0, top-level `axiom` decls 0.
- axiomCount 9 confirmed against the 9 structure-encoded assumptions present in
  source: `gauss_bonnet`, `chi_genus`, `chern_gauss_bonnet`,
  `gauss_bonnet_boundary`, `gauss_bonnet_polygon`, `curvature_is_K_area`,
  `gauss_bonnet_triangle`, `poincare_hopf`, `morse_relation`. The S3-discharged
  `nonvanishing_index` is correctly a derived theorem (via `Finset.sum_empty`),
  not a field.

**Re-open when**: Docker is restored. Resume directly at S4 ACT (Reduction B);
the concrete sketch is in
`sessions/2026-06-09-s2-orient-assumption-inventory.md` §Reduction B and in the
"Active Approach" section below.

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

S6 ACT (Reduction B) complete and docker-verified. Next tractable target is
**Reduction C**: derive `GeodesicTriangle.gauss_bonnet_triangle` from
`ConstCurvatureGeodesicPolygon` at `n := 3` (embed a polygon, relate interior
angles α, β, γ to `exteriorAngleSum = 3π − (α+β+γ)`). ~15 LOC + 1 docker
build. Would bring `axiomCount` 8 → 7. After C, only `curvature_is_K_area`
(cleaner kept as a definitional field, per S3 assessment) and the 6 DEEP
Mathlib-blocked assumptions remain.

## Active Approach

**Reduction C (next)**: restructure `GeodesicTriangle` to carry
`toPolygon : ConstCurvatureGeodesicPolygon` with `n = 3` plus angle fields and
an identification `exteriorAngleSum = (π−α)+(π−β)+(π−γ)` — following the same
embedding pattern as Reductions D and B (embed the general structure, do NOT
try to construct it from loose fields; that direction is circular).

## Attempt Count

- Total attempts: 3 (S2 ORIENT doc-only + S3 ACT Reduction D + S6 ACT Reduction B)
- Current approach attempts: 1 (Reduction B — landed)
- Approaches tried: 3 (S2 inventory survey + S3 Reduction D + S6 Reduction B)

## Blockers

None. Docker restored 2026-07-24; the S4/S5 verification blackout is over.

## Next Action

**Reduction C** — operate on `Proofs/EulerPolyhedralOQ02OQ01.lean` Part XV
(`GeodesicTriangle`, now ~line 553):
1. Embed a `ConstCurvatureGeodesicPolygon` with `n = 3` into `GeodesicTriangle`.
2. Convert `gauss_bonnet_triangle` field to a derived theorem via
   `const_curv_polygon_formula` + exterior/interior angle arithmetic.
3. Verify via `./proofs/scripts/docker-build.sh Proofs.EulerPolyhedralOQ02OQ01`.
4. Update `meta.json` `axiomCount: 8 → 7`.
