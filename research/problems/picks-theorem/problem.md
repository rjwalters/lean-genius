# Problem: Ehrhart Polynomials for 3D Lattice Polytopes

**Slug**: picks-theorem
**Created**: 2026-03-06
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
L_P(n) = \#(nP \cap \mathbb{Z}^d) \text{ is a polynomial of degree } d \text{ in } n
$$
$$
L_P(n) = \text{Vol}(P) \cdot n^d + \frac{1}{2}\text{SurfArea}(P) \cdot n^{d-1} + \cdots + 1
$$

### Plain Language

Generalize Pick's theorem to 3D: for a 3-dimensional lattice polytope P, the number of integer points in the n-th dilation nP is a degree-3 polynomial in n, with leading coefficient equal to the volume. This is Ehrhart's theorem.

### Why This Matters

Ehrhart theory is central to combinatorial geometry, algebraic geometry (toric varieties), and integer programming. It unifies lattice point counting across all dimensions.

## Known Results

### What's Already Proven

- Pick's theorem (2D case) — `proofs/Proofs/PicksTheorem*.lean`
- Mathlib has convex body infrastructure

### What's Still Open

- Ehrhart polynomial formalization in Lean
- Ehrhart reciprocity
- Connection from d=2 specialization to Pick's formula

### Our Goal

Formalize Ehrhart's theorem for d=3, proving polynomiality of the lattice point count.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| picks-theorem | Source — 2D case | Lattice point counting, area decomposition |

## Initial Thoughts

### Potential Approaches

1. **Inclusion-exclusion on faces**: Decompose polytope, count by face contributions
   - Why it might work: Standard proof approach
   - Risk: Face enumeration in Lean is complex

2. **Generating function approach**: Use Ehrhart series = rational function
   - Why it might work: More algebraic, may use Mathlib's formal power series
   - Risk: Requires more algebraic machinery

### Key Difficulties

- Defining lattice polytopes in ℤ^3 cleanly
- Proving polynomiality requires careful induction on dimension
- Connecting back to Pick's theorem as d=2 case

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- Well-known classical result but technically demanding
- Mathlib's polytope support is developing
- The d=1 case (intervals) is a good warmup

## Metadata

```yaml
tags:
  - geometry
  - combinatorics
  - lattice-points
  - ehrhart
related_proofs:
  - picks-theorem
difficulty: medium
source: gallery-gap
created: 2026-03-06
```
