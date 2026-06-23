# Problem: Isoperimetric Theorem — Best Constants in Non-Euclidean Spaces

**Slug**: isoperimetric-theorem-oq-03
**Created**: 2026-04-23
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Plain Language

The classical isoperimetric theorem states that among all plane curves of fixed length,
the circle encloses the maximum area. Quantitatively, for a region with perimeter $L$
and area $A$, the isoperimetric inequality is $4\pi A \leq L^2$, with equality iff
the region is a disk.

**This open question asks**: What are the sharp isoperimetric inequalities in
non-Euclidean spaces (hyperbolic space, spheres, more general Riemannian manifolds),
and can the optimal constants and extremal shapes be formalized in Lean?

In hyperbolic space $\mathbb{H}^n$, the sharp inequality involves geodesic balls.
In spherical geometry, the analogous result holds with spherical caps. In general
Riemannian manifolds, the best constants depend on curvature bounds (Bishop-Gromov
comparison theory).

### Formal Statement

In hyperbolic $n$-space $\mathbb{H}^n$ with curvature $-1$, a domain $\Omega$ with
smooth boundary satisfies:

$$
|\partial \Omega|^n \geq c_n \cdot |\Omega|^{n-1}
$$

where the constant $c_n$ is achieved by geodesic balls, and involves the volume of
geodesic spheres in $\mathbb{H}^n$.

The Lévy-Gromov isoperimetric inequality (on Riemannian manifolds with Ric $\geq K > 0$)
states that the isoperimetric profile of $M$ is bounded below by the profile of the
round sphere $S^n$ with curvature $K/(n-1)$.

### Why This Matters

The isoperimetric problem in non-Euclidean spaces is central to:
1. **Geometric measure theory**: generalizes to arbitrary metric measure spaces
2. **Comparison geometry**: connects curvature bounds to geometric inequalities
3. **Mathematical physics**: soap film shapes in curved space models
4. **Optimal transport**: related to log-Sobolev and Poincaré inequalities

## Known Results

### What's Already Proven

- Euclidean isoperimetric theorem: formalized in gallery (`isoperimetric-theorem`)
- Shapes on other surfaces: formalized in gallery (`isoperimetric-theorem-oq-01`)
- Classical Gauss-Bonnet theorem: formalized in gallery (`triangle-angle-sum-oq-02`)
- Bishop-Gromov comparison: established in differential geometry literature
- Lévy-Gromov inequality: proved by Gromov (1980)

### What's Still Open (in Lean)

- No Lean formalization of sharp isoperimetric constants in $\mathbb{H}^n$
- No formalization of Lévy-Gromov inequality
- Mathlib's Riemannian geometry is still developing

### Our Goal

Formalize at least one sharp isoperimetric inequality in a non-Euclidean setting.
Candidate targets (in order of tractability):
1. **Spherical isoperimetric inequality**: Geodesic balls on $S^n$ are optimal
2. **Discrete analog**: Graph isoperimetric inequality with explicit constants
3. **Hyperbolic**: Sharp inequality for geodesic balls in $\mathbb{H}^2$

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `isoperimetric-theorem` | Parent proof — Euclidean case | Fourier analysis, variational methods |
| `isoperimetric-theorem-oq-01` | Shapes on other surfaces | Surface geometry |
| `triangle-angle-sum-oq-02` | Gauss-Bonnet formalization | Riemannian geometry in Lean |

## Initial Thoughts

### Potential Approaches

1. **Spherical cap optimality on $S^n$**
   - State: among domains on $S^n$ with fixed boundary measure, geodesic caps maximize volume
   - Why it might work: $S^n$ is compact, and Mathlib has `Metric.sphere` infrastructure
   - Risk: sharp constants require careful measure theory on spheres

2. **Graph isoperimetric inequality (discrete analog)**
   - State: for an $n$-vertex graph, the edge boundary of any vertex set
     satisfies an explicit lower bound depending on set size
   - Why it might work: purely combinatorial, no differential geometry needed
   - Risk: this is more combinatorics than geometry

3. **2D Hyperbolic plane**
   - State: geodesic circles maximize area among curves of given hyperbolic length
   - Why it might work: $\mathbb{H}^2$ is well-studied and more approachable
   - Risk: Mathlib's hyperbolic geometry support is limited

### Key Difficulties

- Riemannian manifold machinery in Mathlib is still under active development
- Sharp constants require measure theory on curved spaces
- Need `MeasureTheory.Measure` integration with differential geometry

### What Would a Proof Need?

- Volume form on Riemannian manifolds
- Coarea formula in curved settings
- Symmetrization argument (Steiner or Schwarz symmetrization generalized)
- Or: comparison with constant-curvature model spaces

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Mathlib's Riemannian geometry (`Mathlib.Geometry.Manifold`) exists but is developing
- No existing Lean formalization of sharp isoperimetric constants in curved spaces known
- Spherical or discrete analogs are more approachable than full generality
- Connection to comparison geometry (Lévy-Gromov) requires heavy machinery

**Recommended Starting Point**: Survey what Mathlib has for `Metric.sphere` volume
and `EuclideanSpace` spherical geometry before committing to a specific formulation.

## References

### Papers

- Osserman, R. (1978). "The isoperimetric inequality." *Bull. AMS* 84(6):1182-1238
- Gromov, M. (1980). "Paul Lévy's isoperimetric inequality." *Preprint IHES*
- Chavel, I. (2001). *Isoperimetric Inequalities: Differential Geometric and Analytic Perspectives.* Cambridge

### Mathlib Modules

- `Mathlib.Geometry.Manifold.Basic` — smooth manifolds
- `Mathlib.Analysis.InnerProductSpace.Basic` — inner product spaces
- `Mathlib.MeasureTheory.Measure.Haar.Basic` — Haar measure (for Lie groups)
- `Mathlib.Geometry.Manifold.VectorBundle.Basic` — tangent bundles

## Metadata

```yaml
tags:
  - geometry
  - analysis
  - isoperimetric
  - non-euclidean
  - riemannian-geometry
  - constants
related_proofs:
  - isoperimetric-theorem
  - isoperimetric-theorem-oq-01
  - triangle-angle-sum-oq-02
difficulty: high
tractability: 4
significance: 8
tier: A
source: gallery-gap
created: 2026-04-23
```

**Significance**: 8/10
**Tractability**: 4/10
