# Knowledge Base: euler-polyhedral-formula-oq-02-oq-01-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

The parent gallery proof `Proofs/EulerPolyhedralOQ02OQ01.lean` (786 LOC, namespace `SmoothGaussBonnet`) formalizes the smooth Gauss-Bonnet theorem and its consequences. It has 0 sorries and 0 top-level `axiom` declarations, but it encodes 10 substantive mathematical assumptions as structure fields. The parent `meta.json` correctly reports `axiomCount: 10` per the project's axiom-integrity policy.

This WIP slug asks: which of those 10 structure-encoded assumptions can be replaced with derived Lean theorems against current Mathlib v4.26.0, and which are genuinely blocked by missing Riemannian-geometry infrastructure?

---

## Insights

### S2 (2026-06-09) — Per-field inventory and reduction classification

A complete audit of all 9 structures in the parent file identifies the 10 assumption-carrying fields. Detailed table is in `sessions/2026-06-09-s2-orient-assumption-inventory.md`.

**Summary**: 6 DEEP + 3 TRACTABLE-DERIVABLE + 1 TRACTABLE-CONDITIONAL.

**6 DEEP** (genuinely blocked on missing Riemannian / topology Mathlib infrastructure):
1. `CompactRiemannianSurface.gauss_bonnet` (line 56) — headline GB theorem
2. `OrientableClosedSurface.chi_genus` (line 67) — classification of closed orientable surfaces
3. `ChernGaussBonnetManifold.chern_gauss_bonnet` (line 340) — generalized CGB for 2n-manifolds
4. `CompactSurfaceWithBoundary.gauss_bonnet_boundary` (line 463) — GB with boundary
5. `VectorFieldOnSurface.poincare_hopf` (line 638) — Poincaré-Hopf index theorem
6. `MorseFunctionOnSurface.morse_relation` (line 711) — Morse-Euler identity

**4 TRACTABLE** (reducible without writing new Riemannian geometry):
- `GeodesicPolygon.gauss_bonnet_polygon` (line 486) — corollary of #4 with χ=1 + geodesic-arc identity
- `ConstCurvatureGeodesicPolygon.curvature_is_K_area` (line 494) — `∫ const dx = const · vol`; pure measure theory via `MeasureTheory.setIntegral_const`
- `GeodesicTriangle.gauss_bonnet_triangle` (line 542) — corollary of the polygon GB at n=3 plus exterior/interior-angle algebra
- `VectorFieldOnSurface.nonvanishing_index` (line 640) — if `noZeros` is operationalized as a concrete predicate, this is `Finset.sum_empty`

### S2 Reduction recommendations (cost-ordered)

| Reduction | Field | LOC | Risk |
|-----------|-------|-----|------|
| **D** (do first) | `nonvanishing_index` | ~5 | low — operationalize `noZeros` |
| **B** (do second) | `gauss_bonnet_polygon` | ~10 | medium — needs `toBoundary` coercion |
| **C** (after B) | `gauss_bonnet_triangle` | ~15 | medium — depends on B landing |
| **A** (skip) | `curvature_is_K_area` | ~5 | high — clean reduction blocked by needing #4 first; better to relabel as a *definition* than a theorem |

Best-case S3 outcome: discharge D + B → assumption count 10 → 8 → `axiomCount: 10 → 8` in parent meta.json.

### Mathlib boundary documentation

All 6 DEEP assumptions are blocked on infrastructure not in Mathlib v4.26.0 (pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

| Assumption | Missing Mathlib |
|---|---|
| `gauss_bonnet` | Riemannian metrics; integration of differential 2-forms on oriented manifolds; Gaussian curvature via Weingarten map. |
| `chi_genus` | Classification of closed orientable surfaces up to diffeomorphism. |
| `chern_gauss_bonnet` | Vector bundles with connection; Pfaffian of curvature 2-form; integration on even-dimensional oriented manifolds. |
| `gauss_bonnet_boundary` | Same as gauss_bonnet plus boundary 1-manifold integral. |
| `poincare_hopf` | Vector-field index theory; degree theory on smooth manifolds. |
| `morse_relation` | Morse theory: CW-decomposition via critical points of a Morse function; Morse index. |

These all fit the role's "BLOCKED — Needs > 1000 lines foundational work → Document blocker" category. They should be tracked as MATHLIB GAPS in the problem JSON, not as researcher work items.

---

## Dead Ends

(None yet — S1 was a placeholder; S2 is the first substantive iteration.)

---

## Citations

- Gauss, C. F. (1827). *Disquisitiones generales circa superficies curvas.*
- Bonnet, P. O. (1848). *Mémoire sur la théorie générale des surfaces.*
- Chern, S.-S. (1944). *A simple intrinsic proof of the Gauss-Bonnet formula.*
- do Carmo, M. P. (1976). *Differential Geometry of Curves and Surfaces*, Ch. 4.
- Milnor, J. (1963). *Morse Theory.* — for the Morse-Euler identity, structure assumption #10.
