# Problem: Dirichlet's Approximation via Minkowski's Theorem

**Slug**: minkowski-theorem-oq-02
**Created**: 2026-03-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall \alpha \in \mathbb{R}, \; \forall N \in \mathbb{N}^+, \; \exists p, q \in \mathbb{Z}, \; 1 \leq q \leq N, \; |q\alpha - p| < \frac{1}{N}
$$

Proved as a direct corollary of Minkowski's lattice point theorem applied to the integer lattice $\mathbb{Z}^2$ with an appropriate convex body.

### Plain Language

Dirichlet's approximation theorem says that every real number can be approximated by rationals p/q with |alpha - p/q| < 1/(qN) for some q <= N. The standard proof uses the pigeonhole principle, but it can also be derived elegantly from Minkowski's theorem on lattice points in convex bodies. We want to formalize this derivation in Lean 4.

### Why This Matters

- Demonstrates the power of Minkowski's theorem as a proof technique
- Both theorems are in the Wiedijk 100 list
- The parent Minkowski proof is verified (662 lines, 0 sorries) — strong foundation
- Connects geometry of numbers to Diophantine approximation

## Known Results

### What's Already Proven

- `minkowski-theorem` — Minkowski's lattice point theorem (verified, 662 lines, 0 sorries, 0 axioms)
- Mathlib has Dirichlet's theorem via pigeonhole in various forms
- The gallery proof of Minkowski already handles the convex body framework

### What's Still Open

- Deriving Dirichlet's approximation as a corollary of Minkowski (not via pigeonhole)
- This specific proof path is not formalized anywhere we're aware of

### Our Goal

Formalize Dirichlet's approximation theorem as a direct corollary of the Minkowski lattice point theorem, by applying Minkowski to the rectangle $\{(x,y) : |x| \leq N, |Nx - y| < 1\}$ in $\mathbb{R}^2$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| minkowski-theorem | Parent proof, provides lattice point theorem | Convex bodies, volume bounds, lattice geometry |
| denumerability-rationals | Countability of rationals | Set theory infrastructure |

## Initial Thoughts

### Potential Approaches

1. **Direct application**: Define the convex body $S = \{(x,y) : |x| \leq N+\epsilon, |Nx-y| < 1\}$, show vol(S) > 4, apply Minkowski
   - Why it might work: Clean, direct, uses the existing verified Minkowski proof
   - Risk: Need to interface with the specific API of the Minkowski proof

2. **Symmetric convex body variant**: Use $\{(x,y) : |x| < N+1, |y - \alpha x| < 1/N\}$ with volume $> 4$
   - Why it might work: Standard textbook approach
   - Risk: Same as above

### Key Difficulties

- Interfacing with the Minkowski proof's specific formalization style
- Getting the volume computation through Lean's measure theory
- Extracting the integer lattice point $(q, p)$ with the right properties

### What Would a Proof Need?

- Key lemma: Volume of the rectangle/parallelogram exceeds 4
- Application of Minkowski to get a nonzero lattice point
- Extraction of bounds: $1 \leq q \leq N$ and $|q\alpha - p| < 1/N$

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Parent proof is fully verified with 0 sorries — solid foundation
- The derivation is a standard textbook argument
- Main challenge is interfacing with the existing proof's API

**Estimated Effort**:
- Exploration: 1 day (read Minkowski proof, understand API)
- If tractable: 3-5 days

## References

### Papers
- Cassels, "An Introduction to the Geometry of Numbers" — Chapter on Dirichlet's theorem
- Hardy & Wright, "An Introduction to the Theory of Numbers" — Chapter on approximation

### Mathlib
- `Mathlib.Analysis.Normed.Group.Basic` — Normed group infrastructure
- `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` — Volume computation

## Metadata

```yaml
tags:
  - number-theory
  - geometry
  - lattice
  - diophantine-approximation
  - wiedijk-100
related_proofs:
  - minkowski-theorem
difficulty: medium
source: gallery-gap
created: 2026-03-30
```
