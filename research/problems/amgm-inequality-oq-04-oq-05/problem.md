# Problem: Brent-Salamin Formula: π via AGM and Legendre's Relation

**Slug**: amgm-inequality-oq-04-oq-05
**Created**: 2026-04-26T08:14:40+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\pi = \frac{4 \cdot M(1, 1/\sqrt{2})^2}{1 - \sum_{n=1}^\infty 2^n (a_n^2 - b_n^2)}
$$

where $M(a, b)$ is the arithmetic-geometric mean (AGM), and $(a_n, b_n)$ are the AGM
iteration sequences starting from $(1, 1/\sqrt{2})$.

Equivalently, using Legendre's relation $K(k) K'(k) + K(k') K'(k') = \pi/2$ and the
AGM theorem $M(a, b) = a\pi / (2 K(k'))$, this becomes a theorem about elliptic
integrals.

### Plain Language

The Brent-Salamin formula (1976) computes π using the arithmetic-geometric mean. Starting
from $a_0 = 1$, $b_0 = 1/\sqrt{2}$, iterate $a_{n+1} = (a_n + b_n)/2$,
$b_{n+1} = \sqrt{a_n b_n}$. The AGM $M(1, 1/\sqrt{2})$ converges quadratically, and π
is recovered via the formula above.

The formula follows from Legendre's relation for complete elliptic integrals and the
Gauss AGM theorem connecting K(k) to the AGM.

### Why This Matters

- **Computational significance**: First algorithm for π in O(M(n) log n) bit operations
- **Mathematical depth**: Unifies AGM theory, elliptic integrals, and π in one formula
- **Gallery chain**: Crowns the `amgm-inequality-oq-04` proof tree

## Known Results

### What's Already Proven

- `amgm-inequality-oq-04` (gallery) — AGM basic properties, quadratic convergence
- Mathlib: `Real.sqrt`, `Real.rpow`, interval integrals

### What's Still Open

- Legendre's relation formalized in Lean 4
- Gauss AGM theorem M(a,b) = aπ/(2K(k')) in Lean 4
- Full Brent-Salamin formula assembly

### Our Goal

Formalize the Brent-Salamin formula, building on prerequisites oq-02 (Legendre) and
oq-03 (Gauss AGM theorem). If prerequisites are unavailable, document the gap.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| amgm-inequality-oq-04 | Parent — AGM iteration | AGM, convergence |
| amgm-inequality-oq-04-oq-02 | Legendre's relation (prerequisite) | Elliptic integrals |
| amgm-inequality-oq-04-oq-03 | Gauss AGM theorem (prerequisite) | Hypergeometric series |

## Initial Thoughts

### Potential Approaches

1. **Build the chain**: Verify prerequisites (oq-02, oq-03) then assemble Brent-Salamin.
   - Why it might work: Formula is a direct consequence of Legendre + AGM theorem
   - Risk: Prerequisites may not be formalized yet

2. **Axiomatic statement**: State formula with axioms for missing lemmas, documenting gaps.
   - Why it might work: Valuable formal statement even without full proof
   - Risk: Too many axioms reduces standalone value

### Key Difficulties

- Legendre's relation requires formal elliptic integral theory (outside Mathlib currently)
- The AGM theorem needs the hypergeometric identity K(k) = (π/2)·₂F₁(1/2,1/2;1;k²)

### What Would a Proof Need?

- Prerequisites: Legendre's relation (amgm-inequality-oq-04-oq-02)
- Prerequisites: Gauss AGM theorem (amgm-inequality-oq-04-oq-03)
- Assembly: Derive Brent-Salamin from the above two

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- Mathematics is well-understood (Salamin 1976, Brent 1976, Borwein & Borwein 1987)
- Mathlib lacks complete elliptic integral theory — may need axioms for prerequisites
- With prerequisites done, assembly is tractable (1 week)

**Estimated Effort**:
- Exploration: 1-2 days (check parent proofs and Mathlib status)
- If prerequisites exist: 1 week assembly
- If prerequisites missing: multi-week build

## References

### Papers
- Salamin, E. (1976) — "Computation of π Using Arithmetic-Geometric Mean", *Math. Comp.*
- Brent, R. (1976) — "Fast Multiple-Precision Evaluation of Elementary Functions"
- Borwein & Borwein (1987) — *Pi and the AGM*

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — rpow and sqrt
- `Mathlib.MeasureTheory.Integral.IntervalIntegral` — for K(k) definition

## Metadata

```yaml
tags:
  - analysis
  - agm
  - pi
  - elliptic-integrals
  - brent-salamin
  - seeker-selected
related_proofs:
  - amgm-inequality-oq-04
  - amgm-inequality-oq-04-oq-02
  - amgm-inequality-oq-04-oq-03
difficulty: medium-high
source: gallery-gap
created: 2026-04-26T08:14:40+02:00
```

**Significance**: 8/10
**Tractability**: 5/10
