# Session 2 — 2026-06-09 — ORIENT: inventory of 10 structure-encoded assumptions + reduction plan

**Researcher**: researcher-1
**Problem**: euler-polyhedral-formula-oq-02-oq-01-wip-01
**Status before session**: OBSERVE, iteration 1 (stub knowledge, no concrete plan)
**Mode**: ORIENT (S1 was a placeholder OBSERVE; this session converts the OBSERVE intent into an actionable de-axiomatization plan)
**Outcome**: knowledge — concrete inventory + classification of all 10 structure-encoded assumptions + 4 reducible candidates identified

## Why this session matters

The parent gallery proof `Proofs/EulerPolyhedralOQ02OQ01.lean` (786 LOC, namespace `SmoothGaussBonnet`) is correctly catalogued in `src/data/proofs/euler-polyhedral-formula-oq-02-oq-01/meta.json` with `axiomCount: 10` and a one-line `assumptions:` summary. The WIP slug asked: *which of those 10 can be replaced with a Lean proof against current Mathlib, and which are truly blocked by missing Riemannian infrastructure?* S1 had not yet answered.

S2's contribution: a per-field audit, line by line, with each assumption classified as either (a) deep — genuinely waiting on Riemannian geometry in Mathlib, or (b) tractable — a logical/measure-theoretic identity that can be moved from a structure field to a derived theorem with current Mathlib.

## Inventory of structure fields encoding assumptions

The Lean file has 9 `structure` declarations; the assumption-carrying fields total 10 (matching the parent meta.json count). The mild `area_pos` positivity fields are NOT counted as assumptions in the integrity-policy sense — they are technical positivity premises, not unverified mathematical theorems.

| # | Field | Statement | Line | Classification |
|---|-------|-----------|------|----------------|
| 1 | `CompactRiemannianSurface.gauss_bonnet` | `totalCurvature = 2 * π * chi` | 56 | **DEEP** — the headline GB theorem; needs Riemannian metrics + integration on manifolds. |
| 2 | `OrientableClosedSurface.chi_genus` | `chi = 2 - 2 * (genus : ℤ)` | 67 | **DEEP** — classification of closed orientable surfaces (genus → χ); requires manifold-classification machinery Mathlib lacks. |
| 3 | `ChernGaussBonnetManifold.chern_gauss_bonnet` | generalized CGB for 2n-manifolds | 340 | **DEEP** — Pfaffian of curvature 2-form; needs vector bundles with connection. |
| 4 | `CompactSurfaceWithBoundary.gauss_bonnet_boundary` | `totalCurvature + boundaryGeodCurv = 2 * π * chi` | 463 | **DEEP** — same as #1 plus boundary integral. |
| 5 | `GeodesicPolygon.gauss_bonnet_polygon` | `totalCurvature + exteriorAngleSum = 2 * π` | 486 | **TRACTABLE-derivable** — corollary of #4 applied with χ=1 (disk) and `boundaryGeodCurv = exteriorAngleSum` (geodesic arcs contribute 0; only vertex angles). Convert the field to a theorem. |
| 6 | `ConstCurvatureGeodesicPolygon.curvature_is_K_area` | `totalCurvature = K * area` | 494 | **TRACTABLE** — pure measure theory: `∫_R K dA = K · vol(R)` when `K` is a literal real constant. Mathlib has `MeasureTheory.integral_const` (or `MeasureTheory.setIntegral_const`). Move to a derived theorem. |
| 7 | `GeodesicTriangle.gauss_bonnet_triangle` | `K * area = α + β + γ - π` | 542 | **TRACTABLE-derivable** — corollary of #5 (or #6 with n=3) plus exterior-angle/interior-angle algebra. Move to a derived theorem. |
| 8 | `VectorFieldOnSurface.poincare_hopf` | `totalIndex = surface.chi` | 638 | **DEEP** — Poincaré-Hopf index theorem; needs vector-field/singularity machinery. |
| 9 | `VectorFieldOnSurface.nonvanishing_index` | `noZeros → totalIndex = 0` | 640 | **TRACTABLE if `noZeros` is operationalized** — currently `noZeros : Prop` is abstract, so the field as written IS a free assumption. If `noZeros` is redefined as a concrete predicate "the vector field has no zeros", the field becomes vacuous: an empty sum of indices is `0` by `Finset.sum_empty`. Reduction requires either (a) tightening the structure definition, or (b) keeping it but documenting that this `noZeros` slot is a `Prop`-shaped placeholder, not a topological fact. |
| 10 | `MorseFunctionOnSurface.morse_relation` | `surface.chi = minima - saddles + maxima` | 711 | **DEEP** — Morse–Euler identity; needs CW/cell-decomposition machinery and Morse-theory infrastructure not in Mathlib v4.26.0. |

**Summary**: 6 DEEP + 3 TRACTABLE-DERIVABLE + 1 TRACTABLE-CONDITIONAL. Best-case reduction potential: 10 → 6 assumptions (40% reduction) without writing any new Riemannian geometry.

## Proposed reductions (in order of cost)

### Reduction A — `curvature_is_K_area` (line 494) — pure measure theory

**Cost**: ~5 LOC + 1 docker build. **Confidence**: high (no Riemannian content).

Currently:
```lean
structure ConstCurvatureGeodesicPolygon extends GeodesicPolygon where
  K : ℝ
  curvature_is_K_area : totalCurvature = K * area
```

Replace with:
```lean
structure ConstCurvatureGeodesicPolygon extends GeodesicPolygon where
  K : ℝ
  /-- Predicate: the surface has constant Gaussian curvature K -/
  hasConstCurvature : Prop -- abstract; could be operationalized later
  -- field removed; equivalent statement now derived from CompactSurfaceWithBoundary
```

…but this leaves `totalCurvature = K * area` undischarged. The clean alternative is to **leave the structure but rewrite the field as a derived corollary using a constant-curvature lemma against #4**. This requires #4 to be an axiom OR an additional small axiom `const_curv_total : totalCurvature = K * area_of_region` — net axiom count change is zero, so this reduction only works if we treat `K * area` as a definitional identity (the polygon is *defined* to live on a constant-curvature surface). Best path: relabel the field as a **definition** of "constant curvature polygon" rather than an assumption — no reduction in mathematical content but a correct classification in the meta.json integrity audit.

**S3 ACT recommendation**: skip Reduction A for now; revisit when #4's deep status is addressed.

### Reduction B — `gauss_bonnet_polygon` (line 486) — derive from `gauss_bonnet_boundary`

**Cost**: ~10 LOC + 1 docker build. **Confidence**: medium (depends on whether `GeodesicPolygon` can be made an instance of `CompactSurfaceWithBoundary`).

Currently, `GeodesicPolygon` is a stand-alone structure with no relation to `CompactSurfaceWithBoundary`. The polygon's GB is encoded as a separate field rather than derived.

**Path**: add a `def GeodesicPolygon.toBoundary (P : GeodesicPolygon) : CompactSurfaceWithBoundary` that maps `χ := 1`, `totalCurvature := P.totalCurvature`, `boundaryGeodCurv := P.exteriorAngleSum`, `area := P.area`. The field `gauss_bonnet_polygon` then follows from `(P.toBoundary).gauss_bonnet_boundary`. The polygon structure can drop its `gauss_bonnet_polygon` field. Net assumptions: 10 → 9.

**Risk**: `boundaryGeodCurv` in #4 is the *integrated geodesic curvature*; identifying it with `exteriorAngleSum` is itself a non-trivial discrete identity (Gauss-Bonnet allocates curvature to smooth arcs + vertex contributions). This is a real mathematical claim — but it is provable from #4 by treating arcs as having zero geodesic curvature (geodesic arcs). So the identity is OK *if* we explicitly state the polygon's arcs are geodesic, which the existing `GeodesicPolygon` name already presupposes.

### Reduction C — `gauss_bonnet_triangle` (line 542) — derive from `GeodesicTriangle → ConstCurvatureGeodesicPolygon n=3`

**Cost**: ~15 LOC + 1 docker build. **Confidence**: medium.

After Reduction B, `gauss_bonnet_polygon` is a theorem, not a field. The triangle structure can carry a `toPolygon : ConstCurvatureGeodesicPolygon` with `n := 3`, then `K * area = α + β + γ - π` follows from `const_curv_polygon_formula` + interior-vs-exterior-angle arithmetic. Net assumptions: 9 → 8.

### Reduction D — `nonvanishing_index` (line 640) — operationalize `noZeros`

**Cost**: ~5 LOC + 1 docker build. **Confidence**: high if we accept tightening the structure.

Currently `noZeros : Prop` is an abstract placeholder. Replace with a concrete predicate (e.g., the vector field has no critical points, expressed as some `∀ p, V p ≠ 0`). Then `nonvanishing_index` is `noZeros → totalIndex = 0` which is the trivial "sum over empty set of zeros is 0" — derivable from `Finset.sum_empty`. Net assumptions: 8 → 7.

**Risk**: the existing downstream theorems (`hairy_ball`, `sphere_no_nonvanishing_field`, etc.) consume the field by destructuring `V.nonvanishing_index h`. If `noZeros` is operationalized, downstream usage may need to thread the concrete predicate through. Auditable but careful.

## What S3 ACT should do (concrete starting point)

If S3 has a working Docker build and a 60-min window: attempt Reduction D first (lowest LOC, highest confidence). One file edit + one docker build cycle. If that lands, attempt Reduction B (medium LOC). Skip A; defer C until B lands.

**Expected outcome of an S3 ACT discharging B + D**: assumption count 10 → 8, meta.json `axiomCount: 10 → 8` (parent slug), assumptions string updated. The proof file remains badge `axiomatized` (since the 6 deep ones still gate on missing Mathlib infrastructure), but the slug has measurably honest progress.

## Mathlib boundary documentation (for the 6 deep assumptions)

For completeness, the 6 DEEP assumptions ALL require Mathlib infrastructure not present at v4.26.0 (pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

| Deep assumption | Missing Mathlib infrastructure |
|---|---|
| `gauss_bonnet` (#1) | Riemannian metrics on smooth manifolds; integration of differential 2-forms on oriented manifolds; Gaussian curvature as `tr(W) / 2` where W is the Weingarten map. |
| `chi_genus` (#2) | Classification of closed orientable surfaces up to homeomorphism / diffeomorphism. Mathlib has CW complexes but not the classification theorem. |
| `chern_gauss_bonnet` (#3) | Vector bundles with connection; Pfaffian of curvature 2-form; integration on even-dimensional oriented manifolds. |
| `gauss_bonnet_boundary` (#4) | Same as #1 plus boundary integral over a 1-manifold with measure-theoretic geodesic curvature. |
| `poincare_hopf` (#8) | Index of an isolated zero of a vector field; degree theory on smooth manifolds. |
| `morse_relation` (#10) | Morse theory: CW-decomposition of a manifold via critical points of a Morse function; index of a critical point. |

These all sit in the "BLOCKED — Needs > 1000 lines foundational work → Document blocker" category per the researcher role's WORK CATEGORIES table. They should be tracked as MATHLIB GAPS in the problem JSON, not as researcher work items.

## Files modified

- `research/problems/euler-polyhedral-formula-oq-02-oq-01-wip-01/sessions/2026-06-09-s2-orient-assumption-inventory.md` (this file — new)
- `research/problems/euler-polyhedral-formula-oq-02-oq-01-wip-01/knowledge.md` (S2 inventory + reduction plan)
- `research/problems/euler-polyhedral-formula-oq-02-oq-01-wip-01/state.md` (phase OBSERVE → ORIENT, iteration 1 → 2)
- `src/data/research/problems/euler-polyhedral-formula-oq-02-oq-01-wip-01.json` (lastUpdate, phase, focus, insights, mathlibGaps, nextSteps)

## Knowledge added

- Insights: 1 substantial (10-row per-field inventory with TRACTABLE/DEEP classification and proposed reductions for B/C/D); confirms parent meta.json `axiomCount: 10` is correct.
- Next-steps: 2 concrete (Reduction D first, then Reduction B; defer A and C).
- Built items: 0 (no Lean code changes — same scope-limit posture as S1, plus actionable plan).
