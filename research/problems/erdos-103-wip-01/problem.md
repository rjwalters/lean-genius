# Problem: Complete Erdős Problem #103 — Incongruent Optimal Point Configurations

**Slug**: erdos-103-wip-01
**Created**: 2026-07-09T19:15:58-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
h(n) := \#\Big\{ P \subseteq \mathbb{R}^2 : |P| = n,\ \forall x \neq y \in P\ \|x-y\| \ge 1,\ \operatorname{diam}(P) = D(n) \Big\}\Big/\cong
$$

where $D(n)$ is the minimum diameter of an $n$-point set with pairwise distances at least $1$, and configurations are counted up to congruence. **Question:** does $h(n) \to \infty$ as $n \to \infty$?

### Plain Language

Place $n$ points in the plane so that no two are closer than distance $1$, and make the overall spread (the largest distance between any two points) as small as possible. Such "optimal" configurations need not be unique. $h(n)$ counts how many genuinely different (non-congruent) optimal arrangements exist. Erdős asked whether this count grows without bound as $n$ increases.

### Why This Matters

The problem probes the *diversity* of extremal configurations in discrete geometry, a theme distinct from merely computing the optimum $D(n)$. It is intimately tied to densest circle packing (place $n$ unit-diameter circles in the smallest enclosing circle) where the hexagonal/triangular lattice is asymptotically optimal (Thue–Minkowski). Understanding multiplicity of optima connects extremal geometry, packing theory, and rigidity.

## Known Results

### What's Already Proven

- Thue–Minkowski: the triangular lattice is the densest packing of congruent circles in the plane — provides asymptotic structure of near-optimal configurations.
- Bateman–Erdős and later work on minimum-diameter point sets with prescribed separation give bounds on $D(n)$.
- Gallery entry `erdos-103` formalizes the definitional scaffolding (diameter, separation constraint) in Lean.

### What's Still Open

- Whether $h(n) \to \infty$ (the main conjecture) remains open.
- Even a lower bound $h(n) \ge 2$ for all large $n$ is nontrivial to establish rigorously.

### Our Goal

Complete the work-in-progress gallery formalization `erdos-103`: discharge any remaining `sorry`/scaffolding, state the conjecture as a formal proposition, and formalize whatever partial results (e.g. constructions exhibiting multiple incongruent optima for small $n$, or lattice-based lower-bound families) are attainable in Lean 4 + Mathlib.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-103 | Base WIP entry this problem completes | diameter/separation defs, extremal geometry |
| erdos-99 | Neighboring Erdős distance problem | combinatorial geometry |

## Initial Thoughts

### Potential Approaches

1. **Explicit constructions for small $n$**: exhibit two or more incongruent optimal configurations for concrete $n$ (e.g. triangular-lattice fragments vs. rotated/reflected variants), formalizing the congruence check.
   - Why it might work: small cases are finitely checkable and give a foothold on $h(n) \ge 2$.
   - Risk: proving optimality (that no smaller diameter exists) is the hard part, often requiring case analysis.

2. **Lattice-perturbation families**: near-optimal hexagonal patches admit multiple boundary completions; formalize a family whose size grows with $n$.
   - Why it might work: boundary degrees of freedom naturally multiply configurations.
   - Risk: showing every member is *exactly* optimal (not just near-optimal) is delicate.

### Key Difficulties

- Establishing exact optimality of $D(n)$ is itself hard; multiplicity sits on top of it.
- Congruence classification in $\mathbb{R}^2$ (mod rotations/reflections/translations) is fiddly to formalize.

### What Would a Proof Need?

- Key lemma 1: a rigorous handle on $D(n)$ or a certified lower bound for specific $n$.
- Key lemma 2: a decidable/checkable congruence predicate on finite planar point sets.
- Technical requirements: Mathlib `EuclideanSpace`, `Isometry`, convex geometry lemmas.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The full conjecture $h(n) \to \infty$ is an open problem.
- Formalizing the definitions and small-case multiplicity is a realistic completion target.
- Mathlib has isometry and Euclidean-distance infrastructure but limited discrete-packing results.

**Estimated Effort**:
- Exploration: days
- If tractable (definitions + partial results): weeks
- If hard (full conjecture): unknown

## References

### Papers
- P. Erdős, "Some of my favourite unsolved problems" (1994) [Er94b] — original posing.
- L. Fejes Tóth, "Über die dichteste Zusammenstellung von kongruenten Kreisen in einer Ebene" — densest circle arrangements.
- H. Bateman, P. Erdős, "On the problem of minimum diameter of point sets with prescribed distances."

### Online Resources
- Erdős Problems database, Problem #103 — https://www.erdosproblems.com/103

### Mathlib
- `Mathlib.Analysis.InnerProductSpace.EuclideanDist` / `EuclideanSpace` — planar distances.
- `Mathlib.Topology.MetricSpace.Isometry` — congruence via isometries.

## Metadata

```yaml
tags:
  - combinatorial-geometry
  - packing
  - distances
  - extremal-geometry
related_proofs:
  - erdos-103
  - erdos-99
difficulty: high
source: proof-suggestion
created: 2026-07-09T19:15:58-07:00
```
