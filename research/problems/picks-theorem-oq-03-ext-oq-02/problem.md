# Problem: Reflexive Polytopes and Palindromic h*-Vectors

**Slug**: picks-theorem-oq-03-ext-oq-02
**Created**: 2026-06-25
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
P \text{ reflexive} \;\Longleftrightarrow\; h^*_i = h^*_{d-i}\ \text{for all } i
\quad(\text{the } h^*\text{-vector of } P \text{ is palindromic}).
$$

### Plain Language

For a lattice polytope P, the Ehrhart series encodes the lattice-point counts of its
dilations and has numerator coefficients forming the h*-vector. A polytope is reflexive
when its dual is also a lattice polytope. Hibi's theorem states that reflexivity is
equivalent to the h*-vector being palindromic (symmetric). This extends the parent's
2D Pick-theorem / lattice-point work into Ehrhart theory.

### Why This Matters

Reflexive polytopes are central in toric geometry and mirror symmetry (Batyrev), and
the palindromic-h* characterization (Hibi) is a clean combinatorial criterion. A Lean
formalization would establish a first bridge from elementary lattice-point counting
(Pick) to higher-dimensional Ehrhart theory.

## Known Results

### What's Already Proven

- 2D lattice-point counting / Pick's theorem in the parent picks-theorem-oq-03-ext.
- Basic Finset lattice-point machinery used in the parent.

### What's Still Open

- The Ehrhart polynomial and h*-vector as Lean objects in generality.
- Hibi's palindromic characterization of reflexivity in any dimension.

### Our Goal

Build the minimal Ehrhart / h*-vector infrastructure needed to state the equivalence,
then prove the forward direction (reflexive implies palindromic) in low dimension as a
proof of concept, leveraging Ehrhart reciprocity. Full generality is a stretch goal.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| picks-theorem-oq-03-ext | Direct parent: lattice-point counting in 2D | Pick's theorem, lattice points |
| picks-theorem-oq-03-product | Product-polytope lattice counts | Ehrhart-style counting |

## Initial Thoughts

### Potential Approaches

1. **Ehrhart reciprocity route**: define the Ehrhart polynomial via lattice-point counts,
   prove (or assume) Ehrhart-Macdonald reciprocity, and read palindromy of h* from the
   functional equation relating interior and closed counts.
   - Why it might work: reciprocity directly encodes the i to d-i symmetry.
   - Risk: full reciprocity is a large dependency to formalize from scratch.

2. **Low-dimensional direct check**: in 2D/3D, compute h*-vectors of reflexive examples
   and verify palindromy directly, building intuition and reusable lemmas.
   - Why it might work: concrete, decidable in fixed small dimension.
   - Risk: does not yield the general theorem, only evidence and scaffolding.

### Key Difficulties

- Ehrhart theory is not yet richly developed in Mathlib; much infrastructure is needed.
- Defining the dual polytope and reflexivity cleanly over the integer lattice.

### What Would a Proof Need?

- Key lemma 1: Ehrhart polynomial well-definedness from dilation lattice-point counts.
- Key lemma 2: Ehrhart-Macdonald reciprocity (or a usable special case).
- Technical requirements: lattice polytope / dual-polytope formalization.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Mathlib's Ehrhart support is limited, so substantial groundwork is required.
- The low-dimensional proof of concept is reachable; full generality is a major project.
- The parent gives only 2D lattice-point tools, a modest but real starting point.

**Estimated Effort**:
- Exploration: 3-5 days surveying Ehrhart infrastructure gaps
- If tractable: weeks for a low-dimensional forward direction
- If hard: full Hibi theorem is a long-horizon goal

## References

### Papers
- T. Hibi, Dual polytopes of rational convex polytopes (Combinatorica, 1992).
- V. Batyrev, Dual polyhedra and mirror symmetry (1994).

### Online Resources
- Beck and Robins, Computing the Continuous Discretely (Ehrhart theory textbook).

### Mathlib
- Mathlib.Analysis.Convex.* and Mathlib.LinearAlgebra — convex/lattice scaffolding.

## Metadata

```yaml
tags:
  - combinatorics
  - ehrhart-theory
  - polytopes
related_proofs:
  - picks-theorem-oq-03-ext
difficulty: high
source: proof-suggestion
created: 2026-06-25
```

**Significance**: 6/10
**Tractability**: 4/10
