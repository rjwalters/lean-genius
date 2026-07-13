# Problem: Rödl's Chromatic-Decomposition Construction for r ≥ 3

**Slug**: erdos-1092-oq-02
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Erdős problem #1092 concerns the chromatic decomposition threshold. Rödl's construction resolves the $r = 2$ (bipartite / $\chi = 2$) target. Question: does the construction generalize to $r \ge 3$?

$$
\text{Does Rödl's construction extend from } \chi\text{-target } 2 \text{ to } r \ge 3,
\text{ or does the threshold behavior change for higher chromatic targets?}
$$

### Plain Language

The parent `erdos-1092` studies when a graph's edge set can be decomposed with a prescribed chromatic-threshold behavior; Rödl's construction gives the extremal example for the base ($r=2$) case. This problem asks whether the same construction — and the same threshold — persists when the target chromatic number is raised to $r \ge 3$, or whether a genuinely different phenomenon (a shifted or qualitatively different threshold) emerges.

### Why This Matters

Erdős-type extremal/decomposition thresholds are central to modern combinatorics. Determining whether a known extremal construction is "stable" under raising the chromatic target sharpens understanding of the whole family and is a natural formalization target given the gallery's existing $r=2$ treatment.

## Known Results

### What's Already Proven
- The $r = 2$ case via Rödl's construction — gallery `erdos-1092`.
- Standard chromatic-number and Turán-type API — Mathlib `SimpleGraph`.

### What's Still Open (for formalization)
- Whether Rödl's construction generalizes to $r \ge 3$.
- The correct threshold statement for higher chromatic targets.

### Our Goal
First **survey/decide** (ORIENT phase) whether the mathematical answer is known in the literature. If the generalization holds, formalize the construction and threshold for a fixed small $r$ (e.g. $r = 3$). If it provably fails, formalize the obstruction.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1092 | Direct parent; $r=2$ case | Rödl construction |
| erdos-458-oq-05 | Chromatic/extremal neighborhood | Probabilistic method |

## Initial Thoughts

### Potential Approaches
1. **Lift the construction**: attempt a direct block/product generalization of Rödl's construction with $r$ color classes and check the threshold arithmetic.
2. **Counterexample search**: look for small $r=3$ instances where the $r=2$ threshold fails, indicating changed behavior.

### Key Difficulties
- This is a genuinely research-level extremal question; the literature answer may be unknown, making it exploratory.
- Formalizing extremal graph constructions in Lean is heavy on `Finset`/`SimpleGraph` bookkeeping.

### What Would a Proof Need?
- A clean generalized construction OR a clean obstruction.
- Threshold arithmetic verified for the chosen $r$.

## Tractability Assessment

**Difficulty**: High

**Justification**: Open Erdős-family extremal question; strong ORIENT/survey phase needed before committing. Best suited to a Scout survey followed by a bounded formalization of whichever direction (generalization vs obstruction) the literature supports.

## References

### Papers
- Erdős Problems database, #1092.// V. Rödl, constructions in chromatic/extremal graph theory.

### Mathlib
- `SimpleGraph`, `SimpleGraph.chromaticNumber`, `SimpleGraph.CliqueFree`, Turán-type lemmas.

## Metadata

```yaml
tags:
  - erdos
  - graph-theory
  - chromatic-number
  - extremal-graph-theory
related_proofs:
  - erdos-1092
  - erdos-458-oq-05
difficulty: high
source: gallery-gap
created: 2026-07-04
```
