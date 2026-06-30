# Problem: Cayley–Menger Determinant — Heron's Formula in Higher Dimensions

**Slug**: herons-formula-oq-05
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
288\, V(T)^2 \;=\; \det
\begin{pmatrix}
0 & 1 & 1 & 1 & 1\\
1 & 0 & d_{01}^2 & d_{02}^2 & d_{03}^2\\
1 & d_{01}^2 & 0 & d_{12}^2 & d_{13}^2\\
1 & d_{02}^2 & d_{12}^2 & 0 & d_{23}^2\\
1 & d_{03}^2 & d_{13}^2 & d_{23}^2 & 0
\end{pmatrix},
$$

with $V(T)$ the volume of the tetrahedron on vertices $0,1,2,3$ and $d_{ij}$ the pairwise distances.

### Plain Language

Heron's formula computes the area of a triangle from its three side lengths alone. The Cayley–Menger determinant is the exact higher-dimensional generalization: it expresses the volume of an n-dimensional simplex purely in terms of its pairwise squared edge lengths, with no coordinates. For a tetrahedron (n = 3), 288 times the square of the volume equals the 5×5 Cayley–Menger determinant of the six squared edge lengths. Specializing to n = 2 recovers Heron's formula, and the sign/non-negativity of the determinant encodes whether a given list of distances is realizable as a genuine simplex.

### Why This Matters

The gallery has Heron's formula as a 2D triangle fact. The Cayley–Menger determinant places it in a uniform framework that scales to every dimension and underlies distance geometry, the Euclidean embeddability of metric spaces, and rigidity theory. Formalizing it yields a coordinate-free volume formula and a realizability criterion that are broadly reusable, and it exercises Mathlib's determinant and bilinear-form machinery on a concrete, classical identity.

## Known Results

### What's Already Proven

- `herons-formula` — the n = 2 (triangle area) case, already in the gallery.
- Mathlib provides `Matrix.det`, the Gram matrix / `BilinForm` infrastructure, and `EuclideanSpace`, which together support a coordinate proof of the determinant identity.

### What's Still Open

- A formal definition of the Cayley–Menger matrix from a finite set of pairwise distances.
- The identity 288·V² = det(CM) for the tetrahedron, and its general n-simplex form.
- The realizability theorem: a distance list is Euclidean-embeddable iff the appropriate Cayley–Menger determinants have the correct signs.

### Our Goal

Formalize the Cayley–Menger matrix and prove the tetrahedron identity 288·V² = det(CM), recovering Heron's formula as the n = 2 specialization. A first milestone is reducing the determinant to a Gram determinant via the standard row/column operations, then evaluating the Gram determinant as a squared volume.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| herons-formula | The n = 2 case this generalizes | edge-length area formula |
| pythagorean-theorem | Squared-distance identities in Euclidean space | inner products, orthogonality |
| minkowski-fundamental-theorem | Determinants and lattice/volume reasoning | determinant geometry |

## Initial Thoughts

### Potential Approaches

1. **Approach A (reduce to Gram determinant)**: Apply standard row/column operations to the Cayley–Menger matrix to convert it into (a scalar multiple of) the Gram determinant of edge vectors, whose value is (n! · V)².
   - Why it might work: the Cayley–Menger ↔ Gram reduction is purely algebraic and finite; Mathlib has det manipulation lemmas.
   - Risk: tracking the constant factor (288 for n = 3) and signs across the bordered-determinant manipulation.

2. **Approach B (coordinate placement)**: Place the simplex with vertex 0 at the origin, expand the determinant directly in coordinates, and match to V².
   - Why it might work: fully explicit; avoids abstract bilinear-form lemmas.
   - Risk: heavy symbolic expansion; less reusable for general n.

### Key Difficulties

- Bookkeeping the bordered-determinant (the leading 0 and the row/column of 1's) when reducing to the Gram matrix.
- Pinning the dimensional constant (n! and the factor 288 = 2·(3!)²) and the determinant sign.

### What Would a Proof Need?

- Key lemma 1: Cayley–Menger determinant equals (−1)^{n+1} 2^n (n!)² V² (specialize to n = 3).
- Key lemma 2: Gram determinant of the edge vectors equals (n! · V)².
- Technical requirements: `Matrix.det` row/column operations, Gram matrix lemmas, `EuclideanSpace` volume.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The identity is classical with a short linear-algebra proof; the main cost is formal determinant manipulation.
- The n = 2 (Heron) and n = 3 (tetrahedron) cases are concrete and independently checkable.
- Mathlib's determinant, Gram-matrix, and Euclidean-space libraries cover the needed primitives.

**Estimated Effort**:
- Exploration: 2–3 days
- If tractable: 1–2 weeks
- If hard: unknown (clean general-n statement)

## References

### Papers
- A. Cayley, "On a theorem in the geometry of position" (1841) — origin of the determinant.
- K. Menger, "Untersuchungen über allgemeine Metrik" (1928) — distance-geometry realizability.

### Online Resources
- Cayley–Menger determinant, Wikipedia — explicit matrices, constants, and the Gram reduction.

### Mathlib
- `Mathlib.LinearAlgebra.Matrix.Determinant` — determinant and row/column operations.
- `Mathlib.LinearAlgebra.Matrix.GramSchmidtOrtho` / Gram matrix lemmas — squared-volume evaluation.

## Metadata

```yaml
tags:
  - geometry
  - linear-algebra
  - determinants
  - simplex-volume
related_proofs:
  - herons-formula
  - pythagorean-theorem
difficulty: medium
source: gallery-gap
created: 2026-06-16
```
