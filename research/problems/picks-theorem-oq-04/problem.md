# Problem: Shoelace formula and its integrality bridge to Pick's theorem

**Slug**: picks-theorem-oq-04
**Created**: 2026-06-15T06:15:07.078468+00:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For a simple lattice polygon with vertices } (x_k,y_k)\in\mathbb{Z}^2:\quad 2A = \left|\sum_{k=1}^{m}\big(x_k y_{k+1} - x_{k+1} y_k\big)\right| = 2i + b - 2\quad (\text{indices mod } m)
$$

### Plain Language

Pick's theorem gives the area of a simple lattice polygon as A = i + b/2 − 1, where i and b count interior and boundary lattice points. This task formalizes the shoelace (surveyor's) formula for the area of a polygon from its vertex coordinates, and connects it to Pick's formula via the integrality identity 2i + b − 2 = |Σ(xₖyₖ₊₁ − xₖ₊₁yₖ)|, an arithmetic bridge between the combinatorial lattice-point count and the coordinate area.

### Why This Matters

Pick's theorem is a Wiedijk-100 target; the shoelace bridge makes the area side fully coordinate-computable and links combinatorial and analytic area.

## Classification

```yaml
tier: B
significance: 6
tractability: 6
```

**Significance**: 6/10
**Tractability**: 6/10

## Known Results

### What's Already Proven

- Pick's theorem A = i + b/2 − 1 (gallery base result).
- Mathlib has polygon area / determinant-of-edges machinery to express the shoelace sum.

### What's Still Open

- A clean Lean statement of the shoelace formula for arbitrary simple lattice polygons.
- The integrality identity 2A = 2i + b − 2 tying shoelace to lattice-point counts.

### Our Goal

Formalize the shoelace area formula and prove its equality with Pick's 2i + b − 2 for simple lattice polygons.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| picks-theorem | Parent gallery proof this open question extends |

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Shoelace is a finite determinant sum — directly formalizable.
- The integrality bridge follows from Pick once both sides are stated.
- Main work is the simple-polygon hypotheses and triangulation/induction bookkeeping.

## Metadata

```yaml
tags:
  - geometry
  - combinatorics
  - lattice
  - area
  - wiedijk-100
  - challenging
  - connection
  - gallery-extracted
  - seeker-selected
  - research
related_proofs:
  - picks-theorem
difficulty: medium
source: gallery-gap
created: 2026-06-15T06:15:07.078468+00:00
```
