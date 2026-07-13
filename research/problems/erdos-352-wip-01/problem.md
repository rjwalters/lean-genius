# Problem: Complete Erdős Problem #352 — Triangles of Area 1 in Measurable Sets

**Slug**: erdos-352-wip-01
**Created**: 2026-07-09T19:15:58-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\exists\, c > 0 \ \ \text{such that}\ \ \forall\, A \subseteq \mathbb{R}^2\ \text{measurable with}\ \lambda(A) \ge c,\ \ \exists\, x,y,z \in A\ \text{with}\ \operatorname{area}(\triangle xyz) = 1.
$$

**Question:** does such a threshold $c$ exist? Erdős conjectured the optimal value $c = \dfrac{4\pi}{\sqrt{27}}$.

### Plain Language

If a region of the plane is "big enough" (has Lebesgue measure at least some universal constant $c$), must it contain three of its own points forming a triangle of area exactly $1$? Erdős conjectured yes, with the smallest sufficient area being $4\pi/\sqrt{27}$.

### Why This Matters

The problem lies at the intersection of geometric measure theory and combinatorial geometry: it asks how much *measure* forces a prescribed geometric configuration. It is a continuous analogue of many extremal/Ramsey-type "large object must contain structure" statements, and the conjectured sharp constant hints at an extremal configuration (related to circular/lattice arrangements).

## Known Results

### What's Already Proven

- **Erdős (1978/79, 1984):** sets of *infinite* measure contain unit-area triangles; *unbounded* sets of positive measure contain them. Both follow from the Lebesgue density theorem.
- Partial and conditional bounds on the threshold $c$ appear in the literature; the sharp value $4\pi/\sqrt{27}$ remains conjectural.
- Gallery entry `erdos-352` sets up the measurable-set / triangle-area framing in Lean.

### What's Still Open

- Existence of a *finite* universal threshold $c$ for all measurable sets — the main conjecture.
- The exact optimal constant $c = 4\pi/\sqrt{27}$.

### Our Goal

Complete the WIP gallery formalization `erdos-352`: formalize the statement, the area-of-triangle predicate, and the two Erdős special cases (infinite-measure and unbounded positive-measure sets) via the Lebesgue density theorem. State the general conjecture as a formal proposition; discharge settled scaffolding.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-352 | Base WIP entry this problem completes | Lebesgue measure, density points |
| erdos-103 | Sibling discrete/geometric extremal problem | combinatorial geometry |

## Initial Thoughts

### Potential Approaches

1. **Formalize the special cases via density points**: for infinite-measure or unbounded sets, use `MeasureTheory` density-point machinery to locate three points spanning area $1$.
   - Why it might work: these cases are proven and rely on tools present in Mathlib (Lebesgue density / Vitali).
   - Risk: constructing the explicit triple with exact area $1$ from a density point needs a scaling/continuity argument.

2. **Continuity/scaling lemma**: the area of a triangle on three continuously-moving points takes all values in an interval; combine with positive-measure structure to hit area $1$.
   - Why it might work: intermediate-value + measure positivity is formalizable.
   - Risk: the universal *finite* threshold for bounded sets is the open core and likely out of reach.

### Key Difficulties

- The general bounded-set threshold is open; only special cases are provable.
- Extracting an exact-area-$1$ triangle (not merely "some large triangle") requires a continuity/scaling step.

### What Would a Proof Need?

- Key lemma 1: Lebesgue density theorem applied to $A$ (Mathlib: `MeasureTheory` density results).
- Key lemma 2: triangle-area as a continuous function of three points, with an intermediate-value hit at area $1$.
- Technical requirements: `MeasureTheory.Measure`, `EuclideanSpace`, area via determinant.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The full conjecture (finite universal threshold, sharp constant) is open.
- The Erdős special cases are formalizable and a realistic completion target.
- Mathlib has substantial measure-theory and density-point infrastructure.

**Estimated Effort**:
- Exploration: days
- If tractable (special cases): weeks
- If hard (general threshold): unknown

## References

### Papers
- P. Erdős, [Er78d] (1978/79) and [Er83d] (1984) — original problem and special cases.
- Surveys on geometric measure theory and configurations in positive-measure sets.

### Online Resources
- Erdős Problems database, Problem #352 — https://www.erdosproblems.com/352

### Mathlib
- `Mathlib.MeasureTheory.Covering.Density` — Lebesgue density points.
- `Mathlib.Analysis.InnerProductSpace.EuclideanDist` — planar geometry / area via determinant.

## Metadata

```yaml
tags:
  - geometric-measure-theory
  - lebesgue-measure
  - triangles
  - combinatorial-geometry
related_proofs:
  - erdos-352
  - erdos-103
difficulty: high
source: proof-suggestion
created: 2026-07-09T19:15:58-07:00
```
