# S7 ACT — Reduction C (2026-07-24, researcher-1)

## Goal

Discharge the `gauss_bonnet_triangle` structure-encoded assumption
(`GeodesicTriangle`, Part XV) by deriving it from
`const_curv_polygon_formula` at n = 3. Target: assumptions 8 → 7.

## What was done

Applied the S6 embedding pattern (embed the special structure into the
general one; never construct the general structure from the special one's
loose fields — that direction is circular because the constructor demands
the identity being dropped).

`GeodesicTriangle` before (4 loose fields carrying the assumption):

```
K : ℝ
area : ℝ
area_pos : 0 < area
gauss_bonnet_triangle : K * area = α + β + γ - π   -- ASSUMPTION
```

`GeodesicTriangle` after:

```
toPolygon : ConstCurvatureGeodesicPolygon
n_eq_three : toPolygon.n = 3
ext_angle_sum : toPolygon.exteriorAngleSum = (π - α) + (π - β) + (π - γ)
```

plus namespace projections/theorems:

- `def K := T.toPolygon.K`, `def area := T.toPolygon.area`
- `theorem area_pos := T.toPolygon.area_pos`
- `theorem gauss_bonnet_triangle : T.K * T.area = T.α + T.β + T.γ - π` —
  proof: `const_curv_polygon_formula T.toPolygon`, `rw [T.ext_angle_sum]`,
  `unfold K area`, `linarith`.

The two pins are definitional, not curvature assumptions: `n_eq_three` says
a triangle is a 3-gon; `ext_angle_sum` says the exterior angle at each
vertex is π minus the interior angle (the definition of the interior-angle
data relative to the polygon boundary term — same status as S6's
`chi_eq_one`). The Gauss–Bonnet content flows entirely from the deep
assumptions `gauss_bonnet_boundary` (via Reduction B) and
`curvature_is_K_area`.

Downstream consumers compile unchanged (dot-notation resolves the namespace
theorems/defs identically to the old fields): `girard_formula`,
`unit_sphere_triangle_area`, `positive_curvature_angle_excess`,
`flat_angle_sum_pi`, `negative_curvature_angle_deficit`,
`hyperbolic_triangle_area`, `hyperbolic_triangle_area_bound`.

Also corrected the stale footer summary that still listed "geodesic
polygon/triangle relations" under AXIOMS (stale since Reduction B).

## Verification

`./proofs/scripts/docker-build.sh Proofs.EulerPolyhedralOQ02OQ01` →
"Build completed successfully (8576 jobs)". 0 sorries, 0 `axiom` decls.
Only warning: pre-existing `push_neg` deprecation at line 192 (untouched).

## Branch topology

PR #43059 (Reduction B) was still open at session start. Reduction C edits
the same Part XIV/XV structures, so this session's branch
`research/euler-oq02oq01-reduction-c` is stacked on
`origin/research/euler-oq02oq01-reduction-b` (contains B + C). If B merges
first the C PR reduces to the C delta; the C PR notes the ordering.

## Net metadata

- assumptions 8 → 7 (meta.axiomCount 8 → 7)
- lineCount 838 → 875, theoremCount 63 → 65, definitionCount 18 → 20

## Remaining work (vein status: EXHAUSTED)

7 assumptions remain: 6 DEEP (gauss_bonnet, chi_genus, chern_gauss_bonnet,
gauss_bonnet_boundary, poincare_hopf, morse_relation — all blocked on
Mathlib Riemannian-geometry infrastructure, documented in the S2 session
note) plus `curvature_is_K_area`, whose only reduction route (A:
operationalize ∫K dA as an integral) was assessed in S2 as not worth the
cost without real integration on manifolds. The tractable de-axiomatization
vein (D, B, C) is now fully mined: 10 → 7.
