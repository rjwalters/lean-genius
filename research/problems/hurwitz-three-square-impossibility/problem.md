# Problem: Hurwitz n=3 Impossibility Proof

**Slug**: hurwitz-three-square-impossibility
**Created**: 2025-12-30T16:59:27-08:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\nexists \text{ bilinear } \mu: \mathbb{R}^3 \times \mathbb{R}^3 \to \mathbb{R}^3 \text{ such that } \|\mu(a,b)\|^2 = \|a\|^2 \cdot \|b\|^2
$$

Equivalently: There is no 3-square identity of the form:
$$(a_1^2 + a_2^2 + a_3^2)(b_1^2 + b_2^2 + b_3^2) = z_1^2 + z_2^2 + z_3^2$$
where each $z_i$ is bilinear in $a$ and $b$.

### Plain Language

Hamilton spent 15 years (1828-1843) trying to extend complex numbers to three dimensions. He wanted "triplets" that would do for 3D geometry what complex numbers do for 2D. He finally realized he needed FOUR dimensions (quaternions), not three.

Hurwitz's theorem explains why: there simply cannot be a 3-dimensional normed division algebra. The multiplication structure that preserves norms is mathematically impossible in 3D.

### Why This Matters

1. **Fundamental constraint**: Only 1, 2, 4, 8 dimensions admit such structures
2. **Gallery completion**: Current proof uses an axiom - we want a complete formalization
3. **Demonstrates framework**: This is a genuine research problem requiring Mathlib exploration

## Known Results

### What's Already Proven (in HurwitzTheorem.lean)

- **NSquareIdentity structure**: Definition of n-square identities (lines 74-86)
- **orthogonality_constraint**: If a ⊥ b then mul(a,c) ⊥ mul(b,c) (lines 348-381)
- **orthogonality_constraint_right**: If b ⊥ c then mul(a,b) ⊥ mul(a,c) (lines 385-409)
- **9 image vectors**: m_ij = mul(e_i, e_j) all defined and proven unit norm
- **Cross-term equations**:
  - `hcross_zero: innerProd m₁₁ m₂₃ + innerProd m₁₃ m₂₁ = 0`
  - `hcross_zero2: innerProd m₁₂ m₂₃ + innerProd m₂₂ m₁₃ = 0`
  - `hcross_zero3: innerProd m₂₁ m₃₃ + innerProd m₃₁ m₂₃ = 0`

### What's Still Open

The file uses an axiom at line 420:
```lean
axiom no_three_square_identity_contradiction (nsi : NSquareIdentity 3) : False
```

### Our Goal

Replace this axiom with an actual proof. The comments suggest ~50 lines of case analysis using the geometric constraints.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| hurwitz-theorem | This file | Bilinearity, norm arguments |
| quaternion proofs | n=4 case | Quaternion.normSq_mul |

## Initial Thoughts

### Potential Approaches

1. **Coordinate/matrix approach**
   - Represent vectors explicitly in ℝ³ coordinates
   - The 9 vectors form a 3×3 matrix M
   - Row and column orthonormality → M is orthogonal
   - But bilinearity constraints may force M to have special structure
   - Risk: Heavy coordinate calculations

2. **Subspace decomposition**
   - {m₁₁, m₂₁, m₃₁} is orthonormal basis (column 1)
   - {m₁₁, m₁₂, m₁₃} is orthonormal basis (row 1)
   - Both share m₁₁, so m₁₂, m₁₃ ∈ span{m₂₁, m₃₁}
   - Use Mathlib's orthogonal complement machinery
   - Risk: May need infrastructure not in Mathlib

3. **Direct case analysis on inner products**
   - The equations hcross_zero, hcross_zero2, hcross_zero3 constrain inner products
   - Combined with unit norms, may directly lead to contradiction
   - Risk: Need to identify the right additional constraint

4. **Determinant argument**
   - If rows and columns are orthonormal, det(M) = ±1
   - But other constraints may force det = 0
   - Risk: Need matrix formulation

### Key Difficulties

1. The proof is ~700 lines in, lots of context to manage
2. The exact contradiction isn't clearly identified
3. May need Mathlib linear algebra we haven't explored

### What Would a Proof Need?

- **Key observation**: The 9 unit vectors in ℝ³ with row/column orthonormality constraints are overdetermined
- **Contradiction**: Show some norm equation gives 4 = something ≠ 4, or derive 0 = 1
- **Techniques**: Either coordinate computation or subspace dimension argument

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- Mathematical argument is understood (the constraints overdetermine)
- ~700 lines of setup already done
- Gap is "just" ~50 lines of case analysis
- But: may require Mathlib machinery we need to discover

**Estimated Effort**:
- Exploration: 2-4 hours
- If tractable with current setup: 1-2 days
- If needs new Mathlib machinery: unknown

## References

### Papers
- A. Hurwitz, "Über die Composition der quadratischen Formen", 1898
- John Baez, "The Octonions", Bull. AMS 39 (2002)

### Online Resources
- https://en.wikipedia.org/wiki/Hurwitz%27s_theorem_(composition_algebras)

### Mathlib
- `Mathlib.Analysis.InnerProductSpace.Basic` — orthogonality
- `Mathlib.Analysis.InnerProductSpace.Projection` — orthogonal complements
- `Mathlib.LinearAlgebra.Dimension` — finite dimensional subspaces
- `Mathlib.Algebra.Quaternion` — n=4 case for reference

## Metadata

```yaml
tags:
  - algebra
  - division-algebras
  - composition-algebras
  - hurwitz
related_proofs:
  - hurwitz-theorem
difficulty: medium-high
source: gallery-gap
created: 2025-12-30T16:59:27-08:00
axiom_to_remove: no_three_square_identity_contradiction
file: proofs/Proofs/HurwitzTheorem.lean
line: 420
```
