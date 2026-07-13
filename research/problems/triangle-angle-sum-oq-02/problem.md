# Problem: Triangle Angle Sum: Gauss-Bonnet Theorem Formalization in Lean

## Statement

### Plain Language

Formalize a version of the Gauss-Bonnet theorem in Lean 4 using Mathlib.

The **full** Gauss-Bonnet theorem states that for a compact Riemannian 2-manifold M
without boundary: ∫_M K dA = 2π χ(M), where K is the Gaussian curvature and χ(M) is
the Euler characteristic. This requires differential geometry infrastructure not yet in Mathlib.

The **tractable entry point** is the discrete Gauss-Bonnet theorem (Descartes–Euler): for a
convex polyhedron P with vertices V, edges E, faces F:
  ∑_{v ∈ V} (2π − sum of face angles at v) = 2π χ(P) = 4π

Equivalently (for polyhedra homeomorphic to S²): the total angle defect equals 4π.

### Formal Statement

```lean
-- Discrete Gauss-Bonnet: total angle defect = 4π for convex polyhedra
theorem discrete_gauss_bonnet (P : ConvexPolyhedron) :
    ∑ v : P.Vertices, (2 * π - P.angleSumAt v) = 4 * π := by
  sorry

-- Equivalently: total angle defect = 2π * EulerCharacteristic
theorem discrete_gauss_bonnet_euler (P : Polyhedron) (hP : P.EulerCharacteristic = 2) :
    ∑ v : P.Vertices, angleDefect P v = 2 * π * P.EulerCharacteristic := by
  sorry
```

## Classification

```yaml
tier: A
significance: 8
tractability: 6
tags:
  - geometry
  - gauss-bonnet
  - differential-geometry
  - euler-characteristic
  - polyhedra
  - topology
  - lean4
  - mathlib
```

**Significance**: 8/10 — Connects the elementary Euclidean triangle angle sum to its
deep topological generalization. The Gauss-Bonnet theorem is one of the most important
results in differential geometry. Even the discrete version is a substantial formalization.

**Tractability**: 6/10 — The discrete version avoids differential geometry, using purely
combinatorial machinery. Polyhedra can be modeled with finite simplicial complexes.
Mathlib has `Finset.sum` and angle primitives needed for the combinatorial argument.

## Why This Matters

1. **Natural extension**: The gallery already has `triangle-angle-sum` (∑ angles = π,
   verified) and spherical analogs. Gauss-Bonnet is the capstone of this sequence,
   showing the angle sum as a special case of a topological invariant.

2. **Topology-geometry bridge**: Formalizing even the discrete Gauss-Bonnet shows Lean
   can bridge local geometry (angle defects at vertices) with global topology (Euler
   characteristic).

3. **Methodology**: Demonstrates how to use Mathlib's simplicial complex and Euler
   characteristic infrastructure for geometric applications.

## Existing Infrastructure

The `triangle-angle-sum` gallery proof establishes:
- `triangle_angle_sum : ∀ (a b c : ℝ), isTriangle a b c → a + b + c = π`

Mathlib has:
- `Mathlib.Topology.Algebra.Order` — topological structures  
- `Mathlib.Combinatorics.SimplicialComplex.Basic` — simplicial complexes
- `Mathlib.Analysis.InnerProductSpace.Basic` — angle definitions

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `triangle-angle-sum` | Foundation: Euclidean angle sum (∑ = π) |
| `triangle-angle-sum-oq-01` | Converse: angle sum = π ↔ Euclidean |
| `triangle-angle-sum-oq-03` | Mathlib angle function degenerate cases |
| `spherical-law-of-cosines` | Spherical geometry: angle sum > π |
| `spherical-law-of-sines` | More spherical geometry infrastructure |

## Suggested First Steps

1. **OBSERVE**: Survey `Mathlib.Combinatorics.SimplicialComplex` for polyhedron
   definitions and Euler characteristic. Check if angle defect is already defined.
2. **ORIENT**: Decide between (a) proving the combinatorial Gauss-Bonnet from Euler's
   formula V - E + F = 2, or (b) constructing a `Riemannian2Manifold` instance for S².
3. **DECIDE**: Start with the combinatorial approach: relate angle sums to Euler's formula
   using `2πV - ∑ angles = 2π(V - E + F) = 4π` via the handshaking lemma.

## Known Obstacles

- Mathlib's angle definitions use `EuclideanGeometry.angle` which may need coercions
  for polyhedra vertex angles
- Defining a "convex polyhedron" in Lean may require choosing between simplicial complexes
  and explicit combinatorial structures
- The combinatorial proof requires `∑ face angles = (F - 2)π` (each face is a polygon,
  sum of interior angles), which needs polygon angle sum as a lemma
