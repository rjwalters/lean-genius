# Problem: Ptolemy Theorem — Extension to Spherical and Hyperbolic Geometry

**Slug**: ptolemys-theorem-oq-01-oq-02
**Created**: 2026-04-22
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The classical Ptolemy inequality states: for four points A, B, C, D in the Euclidean plane,

$$|AC| \cdot |BD| \leq |AB| \cdot |CD| + |AD| \cdot |BC|$$

with equality iff the four points are concyclic in that order. Analogues hold in spherical
and hyperbolic geometry — can these be formalized in Lean 4 using Mathlib's metric geometry
infrastructure?

### Plain Language

`ptolemys-theorem-oq-01` formalized the Ptolemy inequality and its equality characterization
(concyclicity) in the Euclidean plane via complex numbers. The question is whether we can
extend this to:

1. **Spherical geometry**: Ptolemy's theorem holds on the sphere (replacing side lengths with
   chord lengths or great-circle distances). The key relation involves `sin` instead of linear
   distances.
2. **Hyperbolic geometry**: A hyperbolic Ptolemy inequality holds in the Poincaré disk/half-plane
   model. The equality case characterizes four points on a hyperbolic circle (horocycle).

### Why This Matters

- **Unification**: A metric-space formulation covers Euclidean, spherical, and hyperbolic cases
  uniformly — this aligns with Mathlib's metric geometry hierarchy.
- **Historical significance**: Ptolemy's original theorem was about chords on a circle, directly
  applicable to spherical trigonometry and navigation.
- **Mathlib contribution potential**: A spherical Ptolemy inequality would complement existing
  `Mathlib.Geometry.Euclidean` and `Mathlib.Analysis.InnerProductSpace` developments.

## Known Results

### What's Already Proven

- `ptolemys-theorem-oq-01`: Full Ptolemy inequality with concyclicity characterization in ℂ
  (0 sorries, verified, original proof)
- Mathlib has `EuclideanGeometry`, `InnerProductSpace`, metric space infrastructure
- Spherical distance is formalized in Mathlib via `Metric.sphere` and `dist`

### What's Still Open

- Spherical Ptolemy inequality in Lean 4
- Hyperbolic Ptolemy inequality in Lean 4
- Whether Mathlib's `Metric.sphere` gives enough structure to state the chord-length version

### Our Goal

Formalize at least one non-Euclidean Ptolemy inequality — preferably the spherical case using
chord lengths (which reduces to the Euclidean case via stereographic projection). If that
succeeds, explore the hyperbolic analogue.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| ptolemys-theorem-oq-01 | Parent proof, Euclidean Ptolemy via ℂ | Complex number algebra, concyclicity |
| ptolemys-complex-proof | Ptolemy inequality via complex cross-ratio | Complex analysis, SameRay |
| feuerbachs-theorem-defs-oq-04 | Connects to Mathlib affine geometry | Affine spaces, Mathlib API |

## Initial Thoughts

### Potential Approaches

1. **Chord-length spherical Ptolemy**: Use stereographic projection to reduce to Euclidean
   Ptolemy. If `f: S² → ℂ ∪ {∞}` is stereographic projection, it sends circles to circles
   and is conformal. The chord-length Ptolemy on S² follows from the Euclidean version.
   - Why it might work: Direct algebraic reduction to existing proof
   - Risk: Stereographic projection may need significant formalization in Mathlib

2. **Direct metric space approach**: Use the CAT(1) property of the sphere and formulate
   Ptolemy in terms of Alexandrov geometry / `CAT κ` spaces.
   - Why it might work: Mathlib has some CAT(0) infrastructure
   - Risk: CAT(1) (positive curvature) is less developed in Mathlib

3. **Möbius transformation approach**: The complex Ptolemy proof extends naturally to the
   Riemann sphere via Möbius transformations, which are the isometries of hyperbolic geometry.
   - Why it might work: Directly generalizes the existing complex proof
   - Risk: Möbius groups in Lean need to be connected to geometric notions

### Key Difficulties

- Stating the "right" metric for spherical/hyperbolic Ptolemy (chord length vs geodesic distance)
- Finding or proving stereographic projection properties in Mathlib
- The equality case (characterizing cycles) may be harder non-Euclidean

### What Would a Proof Need?

- Stereographic projection formalized: `S² → ℂ ∪ {∞}` is conformal and circle-preserving
- Chord distance formula in terms of inner product on S²
- Möbius transformation API in Lean/Mathlib

## Tractability Assessment

**Difficulty**: Medium-High (Challenging)

**Justification**:
- The spherical chord-length version has a clean reduction via stereographic projection
- Mathlib's spherical geometry is partial but growing
- The Euclidean proof is complete and provides a template

**Estimated Effort**:
- Exploration: 2-3 days (survey Mathlib sphere/metric infrastructure)
- If tractable: 1-2 weeks (stereographic projection approach)
- If hard: pivot to a weaker statement (just the inequality, no equality characterization)

## References

### Papers
- Ptolemy, *Almagest* (Book I) — original chord-table motivation
- Schoenberg, "A remark on M.M. Day's characterization of inner product spaces" (1952)
- Foertsch & Schroeder, "Group actions on geodesic Ptolemy spaces" (2011)

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` — sin/cos
- `Mathlib.Geometry.Euclidean.Angle.Sphere` — inscribed angle theorem
- `Mathlib.Topology.MetricSpace.Isometry` — isometry API

## Metadata

```yaml
tags:
  - geometry
  - complex-analysis
  - ptolemy
  - trigonometry
  - concyclicity
  - spherical-geometry
  - hyperbolic-geometry
related_proofs:
  - ptolemys-theorem-oq-01
  - ptolemys-complex-proof
difficulty: challenging
source: gallery-gap
created: 2026-04-22
```

**Significance**: 7/10
**Tractability**: 6/10
