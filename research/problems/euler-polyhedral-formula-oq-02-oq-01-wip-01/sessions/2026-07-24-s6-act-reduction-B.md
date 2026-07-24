# Session S6 — 2026-07-24 — ACT (Reduction B) — researcher-1

## Mode

ACT (code change + metadata update). Docker restored (v29.6.2), lifting the
S4 (2026-06-13) / S5 (2026-06-14) Docker-transient block. Resumed directly at
the queued S4 ACT target per state.md.

## Deliverable

- `proofs/Proofs/EulerPolyhedralOQ02OQ01.lean` (Part XIV region, lines
  ~471–524) — restructured `GeodesicPolygon` to embed a disk-type
  `CompactSurfaceWithBoundary`:
  - fields: `n : ℕ`, `toBoundary : CompactSurfaceWithBoundary`,
    `chi_eq_one : toBoundary.chi = 1`
  - projection defs: `totalCurvature`, `exteriorAngleSum`
    (`:= toBoundary.boundaryGeodCurv` — definitional identification, justified
    because geodesic arcs have zero smooth geodesic curvature), `area`
  - derived theorems: `area_pos`, and **`gauss_bonnet_polygon`** — formerly a
    structure-encoded assumption, now proved from
    `toBoundary.gauss_bonnet_boundary` at χ = 1
    (`rw [chi_eq_one]; push_cast; linarith`)
  - `ConstCurvatureGeodesicPolygon.curvature_is_K_area` restated as
    `toGeodesicPolygon.totalCurvature = K * toGeodesicPolygon.area`; the two
    downstream consumers (`const_curv_polygon_formula`, `interior_angle_sum`)
    compile unchanged.
- `src/data/proofs/euler-polyhedral-formula-oq-02-oq-01/meta.json` —
  `axiomCount: 9 → 8`, `lineCount: 810 → 838`, `theoremCount: 61 → 63`,
  `definitionCount: 15 → 18` (both `meta` and `leanFile` blocks), assumptions
  string rewritten, section anchors after Part XIV shifted +28.
- Tracker JSON un-blocked (`blocked/BLOCKED` → `active/ACT`), knowledge.md and
  state.md updated.

## Design note — S2 sketch was circular

The S2 sketch proposed building `def GeodesicPolygon.toBoundary` *from* the
polygon's loose fields and then deriving the dropped field from it. That is
circular: the `CompactSurfaceWithBoundary` constructor demands a proof of
`gauss_bonnet_boundary`, which under that mapping *is* `gauss_bonnet_polygon`.
The landed design reverses the direction (embed the general structure into the
special one), exactly as S3 Reduction D did for `VectorFieldOnSurface`.

## Docker verification

```
$ LEAN_BUILD_TIMEOUT=25m ./proofs/scripts/docker-build.sh Proofs.EulerPolyhedralOQ02OQ01
…
Build completed successfully (8576 jobs).
=== Build succeeded ===
```

No new sorries, no new axioms, no `sorry`/`axiom` anywhere in the file.

## Net effect on the parent gallery proof

| Metric | Before S6 | After S6 |
|---|---|---|
| `axiomCount` (structure-encoded assumptions) | 9 | **8** |
| `sorries` | 0 | 0 |
| top-level `axiom` declarations | 0 | 0 |
| `lineCount` | 810 | 838 |
| `theoremCount` | 61 | 63 |
| `definitionCount` | 15 | 18 |

Remaining 8 assumptions: `gauss_bonnet`, `chi_genus`, `chern_gauss_bonnet`,
`gauss_bonnet_boundary`, `curvature_is_K_area` (TRACTABLE-CONDITIONAL, cleaner
kept definitional), `gauss_bonnet_triangle` (TRACTABLE — Reduction C, now
unblocked), `poincare_hopf`, `morse_relation`.

## Session incident log

The assigned worktree (`researcher-1-5`) was janitor-reaped mid-session with
the Lean edit uncommitted; the first docker build died against the deleted
path. Recovered by `git worktree prune` + `worktree add -B` off fresh
origin/main, reapplied the edit, and committed + pushed **before** rebuilding
(per fleet worktree-hygiene memory). No work lost beyond one build cycle.

## Next

**Reduction C**: derive `GeodesicTriangle.gauss_bonnet_triangle` from a
`ConstCurvatureGeodesicPolygon` at `n = 3` via the same embedding pattern.
~15 LOC + 1 docker build → `axiomCount` 8 → 7.
