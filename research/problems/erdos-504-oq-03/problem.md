# Problem: Uniqueness of Optimal Configurations for the Maximum-Angle Problem

**Slug**: erdos-504-oq-03
**Created**: 2026-07-03
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\text{For which } N \text{ is the extremal configuration attaining } \alpha_N = \min_{|P| = N}\ \max_{a,b,c \in P}\ \angle(a,b,c)\ \text{unique up to similarity?}
$$

Here $\alpha_N$ is the smallest possible value, over all $N$-point sets $P \subset \mathbb{R}^2$, of the largest angle determined by three points of $P$.

### Plain Language

Erdős Problem #504 (solved by Sendov, 1993) determines $\alpha_N$, the smallest achievable "largest angle" among $N$ planar points. The formula changes at the threshold $N = 5 \cdot 2^{n-3}$ within each dyadic interval $(2^{n-1}, 2^n]$, with two distinct optimal families. This sub-question asks: for which $N$ is the *optimal configuration itself* unique up to similarity (rotation, translation, scaling, reflection), and for which $N$ does a genuine one-parameter (or discrete) family of optima exist?

### Why This Matters

Knowing $\alpha_N$ answers the extremal *value*, but uniqueness of the *extremizer* is a finer structural question: it governs stability of the bound, whether near-optimal sets must resemble the optimum, and whether the binary-threshold phenomenon reflects a rigid combinatorial structure.

## Known Results

### What's Already Proven

- Sendov (1993): exact value of $\alpha_N$, including the $N = 5 \cdot 2^{n-3}$ threshold and the two optimal configuration types — parent entry `erdos-504`.
- Earlier partial results over 50 years bounding the maximum angle.

### What's Still Open

- A complete classification of $N$ for which the extremizer is unique up to similarity.
- Whether non-uniqueness (at threshold $N$) forms a continuum or a finite set of optima.

### Our Goal

Formalize the uniqueness/non-uniqueness dichotomy for small $N$ (e.g. $N \le 8$), establishing which known configurations are the unique minimizers and exhibiting explicit distinct optima where uniqueness fails.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-504 | Direct parent; supplies $\alpha_N$ and the extremal configurations | Discrete geometry, angle optimization |

## Initial Thoughts

### Potential Approaches

1. **Small-case exhaustion**: for fixed small $N$, parameterize configurations and verify the minimizer is (or is not) unique up to the similarity group.
   - Why it might work: low-dimensional; amenable to explicit angle computations.
   - Risk: even $N = 6,7,8$ involve delicate continuous optimization.

2. **Rigidity via the threshold structure**: show the two optimal families coincide exactly at $N = 5 \cdot 2^{n-3}$, forcing non-uniqueness there and uniqueness away from it.
   - Why it might work: aligns uniqueness failure with the known formula break.
   - Risk: requires Sendov's full extremal characterization, not just the value.

### Key Difficulties

- Formalizing "up to similarity" as a group action and reasoning about orbit uniqueness.
- Continuous optimization arguments are hard to make constructive in Lean.

### What Would a Proof Need?

- Key lemma 1: the extremal-value characterization of $\alpha_N$ (from parent entry).
- Key lemma 2: an angle-comparison / rigidity lemma pinning optimal point positions.
- Technical requirements: Euclidean geometry, `EuclideanSpace`, group actions by similarities.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Uniqueness of continuous extremizers is typically harder than the extremal value itself.
- Mathlib's Euclidean-geometry angle API is usable but the optimization is non-trivial.
- Restricting to small $N$ makes a first result plausible.

**Estimated Effort**:
- Exploration: days
- If tractable: weeks
- If hard: unknown

## References

### Papers
- B. Sendov, resolution of the maximum-angle problem (1993).
- P. Erdős, problem list — Problem #504.

### Online Resources
- Erdős Problems database, Problem #504 — https://www.erdosproblems.com/504

### Mathlib
- `EuclideanGeometry.angle` — planar angle definitions.
- `EuclideanSpace ℝ (Fin 2)` — the ambient plane.

## Metadata

```yaml
tags:
  - geometry
  - discrete-geometry
  - extremal-geometry
  - erdos-problem
related_proofs:
  - erdos-504
difficulty: high
source: proof-suggestion
created: 2026-07-03
```

**Significance**: 5/10
**Tractability**: 4/10
