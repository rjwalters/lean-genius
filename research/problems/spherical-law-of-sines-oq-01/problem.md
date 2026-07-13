# Problem: Spherical Excess Formula (Girard-Euler Theorem)

**Slug**: spherical-law-of-sines-oq-01
**Created**: 2026-04-05
**Status**: Active
**Source**: gallery-gap (extension of `spherical-law-of-sines`)

## Problem Statement

### Formal Statement

For a spherical triangle with unit-vector vertices $A, B, C \in \mathbb{R}^3$ (on the unit
sphere) with dihedral angles $\alpha, \beta, \gamma$ at vertices $A, B, C$ respectively:

$$
\alpha + \beta + \gamma = \pi + \Omega
$$

where $\Omega$ is the solid angle (spherical area) of the triangle — the area of the
region on the unit sphere enclosed by the three great-circle arcs.

The solid angle can be expressed via the Van Oosterom–Strackee formula (1983):
$$
\Omega = 2 \arctan\!\left(\frac{|\det[A,B,C]|}{1 + A\cdot B + B\cdot C + C\cdot A}\right)
$$

### Plain Language

Planar triangles have angle sum = π. Spherical triangles have angle sum > π. The excess
$\alpha + \beta + \gamma - \pi$ equals the area of the triangle on the unit sphere.
This is the Girard-Euler theorem (1629/1787).

The recently-verified `spherical-law-of-sines` proof establishes the law of sines using
`projPerp(B,A) × projPerp(C,A) = det[A,B,C]·A`. The excess formula is the next natural
result: it quantifies the total "curvature contribution" of the triangle.

### Why This Matters

- **Foundational**: Cornerstone of spherical geometry and precursor to Gauss-Bonnet
  (integral of Gaussian curvature over a surface = 2π·χ).
- **Formalization gap**: Mathlib has spherical geometry primitives but Girard-Euler appears
  unformalized. Building on the existing `SphericalLawOfSines.lean` framework would give a
  complete elementary treatment.
- **Connections**: Links to Euler characteristic of the sphere, solid angles in 3D, and
  non-Euclidean geometry.

## Known Results

### What's Already Proven

- **`spherical-law-of-sines`** (2026-04-04, verified, 0 sorries):
  `sin²(a)/sin²(α) = sin²(b)/sin²(β)` using the KEY lemma:
  `projPerp(B,A) × projPerp(C,A) = det[A,B,C]·A`
- **Lagrange's identity**: `|u×v|² = |u|²|v|² − (u·v)²`
- **`normSq_projPerp_unit`**: `|projPerp u w|² = sin²(arcLen u w)` for unit u, w
- **`tripleProduct_cyclic`**: `det[A,B,C] = det[B,C,A]`

### What's Still Open

1. Formalization of Girard-Euler in the existing `Fin 3 → ℝ` framework
2. The Van Oosterom-Strackee solid angle formula as a Lean lemma

### Our Goal

Prove `spherical_excess` in Lean 4, building on `SphericalLawOfSines.lean`:

```lean
theorem spherical_excess (A B C : Fin 3 → ℝ)
    (hA : normSq A = 1) (hB : normSq B = 1) (hC : normSq C = 1) :
    dihedralAngle A B C + dihedralAngle B C A + dihedralAngle C A B =
    Real.pi + solidAngle A B C := by
  sorry
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `spherical-law-of-sines` | Direct parent; all definitions and KEY cross-product lemma | projPerp, cross product, triple product |
| `area-of-circle` | Area on curved surfaces | integration, trigonometry |
| `angle-trisection` | Angle arithmetic in Lean 4 | Real.arccos, angle manipulation |

## Initial Thoughts

### Potential Approaches

1. **Direct algebraic via Van Oosterom-Strackee**:
   - Define `solidAngle A B C := 2 * Real.arctan (|det[A,B,C]| / (1 + A·B + B·C + C·A))`
   - Express each dihedral angle using `Real.arctan` (via the existing sin² formulas)
   - Prove the sum = π + solidAngle using arctan addition formulas
   - Risk: significant arctan bookkeeping; Lean's `Real.arctan_add` may be sufficient

2. **Lune area summation (Girard's classical proof)**:
   - Three lunes of angles α, β, γ cover the sphere; the triangle is counted 3 extra times.
   - Area equation: 2α + 2β + 2γ + 2Ω = 4π → α + β + γ = π + Ω
   - Risk: requires defining "lune area" = 2α formally, setting up measure theory for lunes

3. **Axiomatize solidAngle, prove structural properties**:
   - If full proof is too hard, axiomatize `solidAngle_van_oosterom` and prove the excess
     formula as a corollary — still a meaningful formalization
   - Risk: leaves one axiom in place

### Key Difficulties

- Defining `solidAngle A B C` formally in the `Fin 3 → ℝ` framework
- The denominator `1 + A·B + B·C + C·A` can be zero (degenerate triangles) — need hypotheses
- Connecting the algebraic dihedral angle definition to lune areas
- `Real.arctan_add` sum formulas may require sign conditions

### What Would a Proof Need?

- `solidAngle_eq_van_oosterom` — prove the double-arctan formula
- `dihedralAngle_arctan_formula` — express α as arctan in terms of det and dot products
- `arctan_triple_sum` — the relevant arctan addition identity
- Nondegeneracy hypothesis: `det[A,B,C] ≠ 0` or `1 + A·B + B·C + C·A > 0`

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Classical fully-solved result — no mathematical uncertainty
- All algebraic primitives already exist in `SphericalLawOfSines.lean`
- Main challenge: arctan bookkeeping in Lean; `Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan`
  has `Real.arctan_add` and related identities
- Lune approach may be more elegant but needs more definitions

**Estimated Effort**:
- Exploration/OBSERVE: 1 day (check Mathlib arctan API, lune area, existing solid angle work)
- If tractable path found: 2-5 days
- Fallback: axiomatize `solidAngle` definition, prove structural properties (1-2 days)

## References

### Papers
- Girard, A. (1629) — Original statement
- Euler, L. (1787) — Rigorous proof
- Van Oosterom & Strackee (1983) — "The Solid Angle of a Plane Triangle", IEEE Trans. Biomed. Eng.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan` — `Real.arctan_add`
- `proofs/Proofs/SphericalLawOfSines.lean` — parent proof (all needed definitions)

## Metadata

```yaml
tags:
  - geometry
  - spherical-geometry
  - trigonometry
  - non-euclidean-geometry
  - cross-product
  - girard-euler
related_proofs:
  - spherical-law-of-sines
  - area-of-circle
difficulty: medium
source: gallery-gap
created: 2026-04-05
```

**Significance**: 6/10
**Tractability**: 6/10
