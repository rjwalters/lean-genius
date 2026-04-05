# Problem: Prove 2D Brouwer Fixed Point via Sperner's Lemma

**Slug**: brouwer-fixed-point-oq-01-oq-01
**Created**: 2026-04-05
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The gallery entry `brouwer-fixed-point` axiomatizes the full n-dimensional Brouwer
Fixed Point Theorem. The 2D case — every continuous function from the closed disk
to itself has a fixed point — is the most geometrically intuitive instance and
admits a combinatorial proof via Sperner's Lemma.

The goal is to produce a fully-verified Lean 4 proof of the 2D Brouwer Fixed Point
Theorem using the triangulation-based Sperner's Lemma approach, without axioms.

Key steps:
1. Triangulate the closed disk (standard 2-simplex)
2. Apply Sperner's Lemma (already proved in `SpernerNDim.lean`)
3. Extract a fixed-point sequence from the sequence of fully-colored simplices
4. Use compactness to obtain a convergent subsequence
5. Show the limit is a fixed point by continuity

### Plain Language

Given any continuous function `f : D² → D²` (from the closed unit disk to itself),
there exists `x ∈ D²` with `f(x) = x`. The proof strategy:
- Triangulate D² finely
- Color vertices by which coordinate of `x - f(x)` is most negative (Sperner coloring)
- Sperner's Lemma guarantees a fully-colored triangle exists
- As mesh size → 0, these triangles shrink to a point — which must be a fixed point

### Why This Matters

This is one of the most elegant proofs in combinatorial topology: reducing a
topological theorem to a purely combinatorial fact (Sperner's Lemma). Since
`SpernerNDim.lean` is already fully verified, this proof can potentially achieve
`badge: "original"` (0 axioms) rather than the current `badge: "axiom"` of the
main `BrouwerFixedPoint.lean` entry. It also provides a verified bridge between
the combinatorial Sperner infrastructure and classical topology.

## Known Results

### What's Already Proven in the Gallery

- `SpernerNDim.lean` — n-dimensional Sperner's Lemma (VERIFIED, 0 axioms, 0 sorries)
- `BrouwerFixedPointOQ01.lean` — 1D Brouwer via IVT (VERIFIED, 0 axioms)
- `BrouwerFixedPoint.lean` — Full n-dim Brouwer (axiomatized, badge: "axiom")
- Mathlib: `IsCompact.closedBall`, `Metric.closedBall`, `ContinuousMap`

### What's Still Open

- No `BrouwerFixedPointOQ01OQ01.lean` exists yet
- The Sperner-to-Brouwer bridge for 2D is not formalized in this gallery
- The compactness argument extracting a fixed point from approximations

### Our Goal

Prove: `theorem brouwer_2d : ∀ f : C(closedBall 0 1, closedBall 0 1), ∃ x, f x = x`

Target: 0 axioms, 0 sorries — `badge: "original"`

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `sperner-ndim` | Key ingredient: Sperner's Lemma is verified here |
| `brouwer-fixed-point` | Parent proof (n-dim, axiomatized) |
| `brouwer-fixed-point-oq-01` | 1D case via IVT (similar compactness limit argument) |
| `brouwer-fixed-point-oq-01-oq-03` | Borsuk-Ulam via Brouwer (related equivalence chain) |

## Initial Thoughts

### Potential Approaches

1. **Direct Sperner triangulation of the 2-simplex**:
   - The standard 2-simplex (triangle) is homeomorphic to D²
   - Use `SpernerNDim` with d=2, N=n (refinement)
   - Define Sperner coloring from `f(x) - x`: color vertex `v` by the index `i`
     where `(v - f(v))_i = max_j (v - f(v))_j ≥ 0`
   - Sperner guarantees a fully-colored 2-simplex at each level n
   - Diagonal/compactness argument: subsequence converges by Bolzano-Weierstrass
   - At the limit point, `f(x) = x` by continuity

2. **Use existing Mathlib fixed-point results**:
   - Check if Mathlib has `Continuous.fixedPoint` for compact convex sets
   - `Mathlib.Topology.Algebra.Module.FiniteDimension` may have related results
   - If Mathlib already has it, may just need `exact Mathlib.lemma_name`

3. **Kakutani / Schauder approach** (overkill for 2D):
   - Not recommended for this specific case

### Key Difficulties

- Bridging `SpernerNDim` (abstract triangulation) to the concrete disk requires
  a homeomorphism from the standard 2-simplex to D²
- The compactness argument needs `Metric.isCompact_closedBall` and sequential
  compactness for ℝ²
- Defining the Sperner coloring from `f` requires showing it satisfies the
  boundary condition

### What Would a Proof Need?

- **Homeomorphism**: `Simplex 2 ≃ₜ closedBall (0 : ℝ²) 1`
- **Sperner coloring from f**: A function `color_vertex : Vertex 2 N → Fin 3`
  satisfying the Sperner boundary condition relative to `f`
- **Approximation sequence**: `x_n ∈ simplex_n` with `‖x_n - f(x_n)‖ ≤ C/n`
- **Limit argument**: `x_n` subconverges to `x*` with `f(x*) = x*`

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical argument is classical and well-understood
- `SpernerNDim.lean` is already verified — the hard part is done
- The compactness argument is standard (sequential compactness of closed balls)
- The main challenge: bridging abstract `SpernerNDim` structure to a concrete coloring
  defined by `f` — requires careful instance construction
- Risk: Lean 4 homeomorphism definitions for simplex ≃ disk may be verbose

**Estimated Effort**: 3-5 researcher iterations

## References

### Mathlib
- `Mathlib.Topology.MetricSpace.Basic` — `Metric.closedBall`, `isCompact_closedBall`
- `Mathlib.Topology.Compactness.Compact` — `IsCompact`, sequential compactness
- `Proofs.SpernerNDim` — n-dim Sperner's Lemma (fully verified)
- `Mathlib.Analysis.InnerProductSpace.PiL2` — `EuclideanSpace`, `ℝ²`

### Literature
- Brouwer, L.E.J. (1911) — Original theorem
- Cohen, D.I.A. (1967) — Combinatorial proof via Sperner
- Su, F.E. (1999) — "Rental Harmony: Sperner's Lemma in Fair Division" — clear exposition

## Metadata

```yaml
tags:
  - topology
  - combinatorics
  - fixed-point-theory
  - sperner
  - compactness
  - technique
related_proofs:
  - sperner-ndim
  - brouwer-fixed-point
  - brouwer-fixed-point-oq-01
  - brouwer-fixed-point-oq-01-oq-03
difficulty: medium
source: gallery-gap
created: 2026-04-05
```

**Significance**: 7/10
**Tractability**: 6/10
