# Problem: Petr–Douglas–Neumann Generalization of Napoleon's Theorem

**Slug**: napoleons-theorem-oq-03
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For } P \in \mathbb{C}^n,\quad \mathrm{PDN}_{k_{n-2}} \circ \cdots \circ \mathrm{PDN}_{k_1}(P)\ \text{is a regular } n\text{-gon},
$$

where $\mathrm{PDN}_k$ erects on each edge of the current polygon a similar isosceles triangle with apex angle $k\pi/n$ and replaces vertices by apices, applied once for each $k \in \{1,\dots,n-2\}$.

### Plain Language

Napoleon's theorem says that if you erect equilateral triangles outward on the three sides of any triangle, their centroids form an equilateral triangle. The Petr–Douglas–Neumann (PDN) theorem is the full generalization to polygons: given an arbitrary planar n-gon, repeatedly apply the operation "erect similar isosceles triangles on each side and take their apex points as the new vertices," using apex angle kπ/n at step k. After n−2 such steps (one for each k = 1, …, n−2) the resulting n-gon is always regular. Napoleon's theorem is exactly the n = 3 case (a single step produces an equilateral triangle).

### Why This Matters

The gallery contains Napoleon's theorem as an isolated planar-geometry fact. PDN reveals it as the first instance of a clean spectral phenomenon: identifying a polygon with a vector in ℂⁿ, each PDN step annihilates one Fourier mode of the vertex sequence, and a polygon is regular precisely when only a single nonzero mode survives. Formalizing PDN builds reusable infrastructure connecting elementary Euclidean geometry to the discrete Fourier transform and circulant operators, and showcases how roots of unity linearize a sequence of geometric constructions.

## Known Results

### What's Already Proven

- `napoleons-theorem` — the classical n = 3 equilateral-centroid result, already in the gallery.
- Mathlib provides `Complex`, roots of unity (`Complex.isPrimitiveRoot_exp`), and finite-dimensional inner product geometry usable to model planar polygons as elements of ℂⁿ.

### What's Still Open

- A formal definition of the PDN operation as a ℂ-linear (circulant) map on ℂⁿ.
- The spectral lemma that step k kills the k-th DFT coefficient, and the characterization of regular n-gons by a single surviving mode.
- The assembled theorem for general n, with Napoleon recovered as a corollary.

### Our Goal

Formalize the PDN construction over ℂ and prove that the (n−2)-fold composition sends every n-gon to a regular n-gon, via the discrete Fourier decomposition of the vertex vector. A concrete first milestone is the n = 4 case (one extra step beyond Napoleon), then the general circulant/eigenvalue argument.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| napoleons-theorem | The n = 3 special case this generalizes | complex coordinates, rotations by cube roots of unity |
| euler-identity | Roots of unity and complex exponentials underpin the DFT argument | complex exponential algebra |
| fundamental-theorem-algebra | Polynomial/roots-of-unity machinery over ℂ | factorization over ℂ |

## Initial Thoughts

### Potential Approaches

1. **Approach A (spectral / DFT)**: Encode the polygon as v ∈ ℂⁿ; show each PDN step is multiplication of the DFT coordinates by a fixed factor, with the step-k factor vanishing on mode k.
   - Why it might work: turns an iterated geometric construction into a diagonal linear map; regularity ⇔ support is a single mode.
   - Risk: bookkeeping for which apex-angle/orientation convention produces the clean factor; matching geometric "isosceles apex" to the complex multiplier.

2. **Approach B (direct circulant linear algebra)**: Represent each step as a circulant matrix and diagonalize simultaneously in the Fourier basis.
   - Why it might work: circulants commute and share the DFT eigenbasis, giving the composition's spectrum directly.
   - Risk: formalizing circulant diagonalization in Mathlib may require building supporting lemmas.

### Key Difficulties

- Choosing an orientation/apex-angle convention that makes the per-step Fourier multiplier exactly vanish on the intended mode.
- Defining "regular n-gon" in a form (single nonzero DFT mode up to translation) that the spectral argument can target directly.

### What Would a Proof Need?

- Key lemma 1: PDN_k acts on ℂⁿ as a circulant map whose Fourier symbol vanishes at frequency k.
- Key lemma 2: a polygon is regular iff its DFT is supported on the constant mode plus one primitive frequency.
- Technical requirements: DFT over ℂⁿ, roots of unity, circulant/eigenvalue facts.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The mathematics is fully classical and the spectral proof is short on paper, but the formalization requires building DFT/circulant scaffolding not yet packaged in Mathlib.
- Similar spectral-geometry formalizations exist piecemeal; the n = 3 and n = 4 cases are concrete and checkable.
- Mathlib supplies ℂ, roots of unity, and linear algebra, but discrete Fourier transform support is thin.

**Estimated Effort**:
- Exploration: 2–4 days
- If tractable: 2–3 weeks
- If hard: unknown (general-n spectral assembly)

## References

### Papers
- K. Petr, "Ein Satz über Vielecke" (1908) — original statement.
- J. Douglas, "Geometry of polygons in the complex plane" (1940) — complex/DFT proof.
- B. H. Neumann, "Some remarks on polygons" (1941) — independent rediscovery.

### Online Resources
- Petr–Douglas–Neumann theorem, Wikipedia — statement, conventions, and the Fourier proof sketch.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle` and roots-of-unity lemmas — DFT building blocks.
- `Mathlib.LinearAlgebra` (circulant/eigenvalue support) — diagonalization in the Fourier basis.

## Metadata

```yaml
tags:
  - geometry
  - complex-analysis
  - fourier
  - polygons
related_proofs:
  - napoleons-theorem
  - euler-identity
difficulty: high
source: gallery-gap
created: 2026-06-16
```
