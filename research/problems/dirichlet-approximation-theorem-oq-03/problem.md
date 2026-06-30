# Problem: Dirichlet Approximation via Minkowski's Convex-Body Argument

**Slug**: dirichlet-approximation-theorem-oq-03
**Created**: 2026-06-19T17:27:54-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

Dirichlet's approximation theorem: for every real $\alpha$ and every integer $N \ge 1$ there exist
integers $p, q$ with $1 \le q \le N$ such that

$$
\left| \alpha - \frac{p}{q} \right| < \frac{1}{q\,N} \quad\Bigl(\text{equivalently } |q\alpha - p| < \tfrac{1}{N}\Bigr).
$$

The current gallery entry proves this via an explicit pigeonhole interval map. This problem asks two
related questions:

1. **Subsumption**: Does Mathlib's continued-fraction development already provide this bound (or a
   stronger one, $|q\alpha - p| < 1/q$ for infinitely many $q$)?
2. **Minkowski route**: Can the explicit interval/pigeonhole construction be replaced by **Minkowski's
   convex-body theorem** (geometry of numbers) — applied to the symmetric convex region
   $|x| \le N,\ |\alpha x - y| \le 1/N$ in $\mathbb{R}^2$ — yielding the same bound?

### Plain Language

Every real number can be approximated by a fraction $p/q$ with denominator at most $N$ to within
$1/(qN)$. The gallery proves this by pigeonhole. We want to know whether the slicker lattice-point
proof (Minkowski: a symmetric convex body of area $> 4$ contains a nonzero lattice point) can be
formalized for the same result, and whether Mathlib's continued fractions already give it.

### Why This Matters

Minkowski's theorem is the canonical "geometry of numbers" entry point and generalizes to
simultaneous Diophantine approximation in higher dimensions. Re-deriving Dirichlet through it tests
whether Mathlib's `GeometryOfNumbers` / convex-body API is usable here and opens a path to the
multidimensional Dirichlet theorem.

## Known Results

### What's Already Proven

- `dirichlet-approximation-theorem` — gallery entry: the $1/(qN)$ bound via pigeonhole on fractional
  parts (`Proofs/DirichletApproximation.lean`).
- Mathlib `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` — Minkowski's
  convex-body theorem (compact, area-`= 2ⁿ` variant).
- Mathlib continued-fraction development (`Mathlib.Algebra.ContinuedFractions.*`,
  `abs_sub_convergents_le'`).

### What's Still Open

- The volume computation `volume (body α N) = 4` feeding the Minkowski lemma.
- Whether Mathlib's continued fractions yield the Dirichlet bound directly (and at what strength).

### Our Goal

Give a sorry-free Minkowski-convex-body proof of Dirichlet's bound, or establish the
continued-fraction subsumption; compare both to the existing pigeonhole proof.

## Tractability Assessment

**Difficulty**: Medium. Both routes are classical and short on paper; the obstacle is Mathlib API
alignment (the convex-body volume computation and the lattice fundamental domain).

## References

- G. L. Dirichlet (1842) — the pigeonhole approximation theorem.
- H. Minkowski — geometry of numbers / convex-body theorem.
- `Mathlib.MeasureTheory.Group.GeometryOfNumbers`, `Mathlib.Algebra.Module.ZLattice.*`.

## Metadata

```yaml
tags:
  - number-theory
  - diophantine-approximation
  - geometry-of-numbers
  - minkowski
  - continued-fractions
related_proofs:
  - dirichlet-approximation-theorem
difficulty: medium
source: proof-suggestion
created: 2026-06-19T17:27:54-07:00
```
