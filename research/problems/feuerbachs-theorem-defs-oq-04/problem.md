# Problem: Feuerbach's Theorem: Connect to Mathlib Affine Geometry Framework

## Statement

### Plain Language

The existing `FeuerbachsTheoremDefs.lean` formalizes the nine-point circle and incircle
tangency using a **custom coordinate API** (`Point = ℝ × ℝ`, `dist2`, `Triangle` structure).
OQ-04 asks: can we reformulate these results using **Mathlib's abstract affine and Euclidean
geometry framework** for a more algebraic, dimension-independent treatment?

Concretely: define the nine-point circle as a `Sphere` (from `Mathlib.Geometry.Euclidean.Sphere`)
in `EuclideanSpace ℝ (Fin 2)`, prove the nine key points lie on it, and express tangency via
Mathlib's `dist`-based sphere API rather than the custom `circlesInternallyTangent` predicate.

### Formal Statement

```lean
-- Desired form: abstract Sphere version of ninePointCircleContainsAllNinePoints
theorem ninePointCircle_nine_points_sphere
    (T : Triangle) (hnt : T.is_nondegenerate) :
    let pts := [T.midpoint_a, T.midpoint_b, T.midpoint_c,
                T.foot_a, T.foot_b, T.foot_c,
                T.midpoint_AH, T.midpoint_BH, T.midpoint_CH]
    ∀ p ∈ pts, dist (toEuclidean T.ninePointCenter) (toEuclidean p) =
               T.ninePointRadius := by
  sorry

-- And a sphere-based tangency:
theorem incircle_tangent_to_ninePointCircle_sphere
    (T : Triangle) (hnt : T.is_nondegenerate) :
    dist (toEuclidean T.ninePointCenter) (toEuclidean T.incenter) =
    T.ninePointRadius - T.inradius := by
  sorry
```

## Classification

```yaml
tier: B
significance: 7
tractability: 7
tags:
  - geometry
  - feuerbach
  - mathlib
  - affine-geometry
  - formalization
  - euclidean-space
  - sphere
```

**Significance**: 7/10 — Connects gallery proof to Mathlib's preferred geometry API,
enabling potential Mathlib contribution and more elegant downstream proofs.

**Tractability**: 7/10 — The hard mathematical work is done; this is primarily a
translation/bridging task between two Lean APIs. Requires Mathlib familiarity.

## Why This Matters

1. **Mathlib alignment**: Mathlib uses `EuclideanSpace ℝ (Fin n)` and `Sphere` types;
   the gallery proof uses a bespoke coordinate system. Bridging them enables reuse.
2. **Dimension abstraction**: Mathlib's framework scales to `Fin n`; a proof in this
   setting can generalize Feuerbach-like tangency results.
3. **Reusable API**: `toEuclidean` conversion lemmas would benefit other gallery proofs
   that currently duplicate the same custom coordinate infrastructure.

## Existing Infrastructure

```
proofs/Proofs/
  FeuerbachsTheoremDefs.lean      -- Custom Point/Triangle definitions (base)
  FeuerbachsTheoremDefsOQ03.lean  -- Feuerbach point uniqueness (uses custom API)
  FeuerbachsTheoremOQ01.lean      -- Main tangency results
  FeuerbachsTheorem.lean          -- Assembly
```

**Key existing types** (in `FeuerbachsTheorem` namespace):
- `Point = ℝ × ℝ`
- `dist2 P Q : ℝ` — Euclidean distance (NOT squared, despite the name)
- `Triangle` structure with `A B C : Point` fields
- `circlesInternallyTangent` — custom tangency predicate

**Mathlib targets**:
- `Mathlib.Geometry.Euclidean.Sphere.Basic` — `Sphere` type, membership
- `Mathlib.Geometry.Euclidean.Circumcenter` — circumcenter, nine-point center
- `Mathlib.Geometry.Euclidean.Triangle` — triangle defs
- `EuclideanSpace ℝ (Fin 2)` — the abstract plane

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `FeuerbachsTheoremDefs.lean` | Source of the custom API to be bridged |
| `FeuerbachsTheoremDefsOQ03.lean` | Feuerbach point uniqueness (same custom API) |
| `sperner-ndim` | Example using `EuclideanSpace ℝ (Fin n)` |

## Suggested First Steps

1. **OBSERVE**: Check what Mathlib's `Sphere` type looks like and what lemmas exist for
   membership/tangency. Search: `Mathlib.Geometry.Euclidean.Sphere.Basic` definitions.
2. **ORIENT**: Define `toEuclidean : Point → EuclideanSpace ℝ (Fin 2)` and prove
   `dist (toEuclidean P) (toEuclidean Q) = dist2 P Q` as a bridge lemma.
3. **DECIDE**: Can we state the nine-point membership theorem directly via this bridge,
   or do we need to reformulate from scratch using Mathlib types throughout?

## Known Obstacles

- `dist2` naming in `FeuerbachsTheoremDefs.lean` is confusing (it is actual distance,
  not distance squared); verify before bridging.
- Mathlib's `EuclideanGeometry.circumcenter` may use a different characterization than
  the explicit coordinate formula in the gallery.
- `circlesInternallyTangent` uses a 3-tuple encoding; Mathlib uses `Sphere` with
  `center : E` and `radius : ℝ`.
