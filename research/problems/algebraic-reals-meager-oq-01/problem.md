# Problem: Package the Full Baire Category Theorem for Perfect Polish Spaces

**Slug**: algebraic-reals-meager-oq-01
**Created**: 2026-06-19T17:27:54-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

The `algebraic-reals-meager` entry formalized the abstract uncountability theorem

$$
\texttt{not\_countable\_of\_perfect\_t1\_baire} : \; X \text{ nonempty, } T_1, \text{ perfect, BaireSpace} \;\Longrightarrow\; \neg\, \text{Countable } X.
$$

Goal: pair this with an **arbitrary perfect Polish space** to package the Baire Category Theorem at
that level of generality — i.e. expose the general statement "a nonempty perfect Polish space is
uncountable" (and the supporting "complete metric space is a `BaireSpace`") as a reusable gallery
result. The $\mathbb{R}$ instance `not_countable_real` already subsumes the companion nested-interval
entry.

### Plain Language

We already proved, abstractly, that a topological space with no isolated points (perfect), mild
separation ($T_1$), and the Baire property cannot be countable. Polish spaces (separable, completely
metrizable) are automatically Baire. So "perfect + Polish ⟹ uncountable" should follow by feeding a
perfect Polish space into the abstract theorem. The task is to assemble that instantiation cleanly.

### Why This Matters

This converts a one-off ($\mathbb{R}$-specific) uncountability result into the general descriptive
set theory statement, which is the standard form (e.g. "every nonempty perfect Polish space is
uncountable"). It strengthens the gallery's coverage of Baire-category arguments and makes the
abstract theorem demonstrably reusable.

## Known Results

### What's Already Proven

- `not_countable_of_perfect_t1_baire` — `algebraic-reals-meager` entry: the abstract uncountability
  theorem.
- `not_countable_real` — the $\mathbb{R}$ instance, already subsuming the nested-interval companion.

### What's Still Open

- The general packaging: "nonempty perfect Polish space ⟹ uncountable."
- Confirming the cleanest Mathlib path from `PolishSpace`/`CompleteSpace` to `BaireSpace` and $T_1$.

### Our Goal

State and prove, sorry-free, the general theorem for perfect Polish spaces by instantiating the
existing abstract theorem; verify $\mathbb{R}$ and Cantor space $2^{\mathbb{N}}$ fall out as
corollaries.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| algebraic-reals-meager | Provides the abstract theorem to instantiate | Baire category, perfect sets |
| (nested-interval uncountability companion) | Subsumed by `not_countable_real` | nested intervals |

## Initial Thoughts

### Potential Approaches

1. **Direct instantiation**: Show `PolishSpace X → BaireSpace X` (Mathlib: complete metric ⟹ Baire)
   and `T1Space X`, then apply `not_countable_of_perfect_t1_baire`.
   - Why it might work: each hypothesis is a known Mathlib instance for metric/Polish spaces.
   - Risk: locating the exact `BaireSpace` instance lemma and `Perfect`/no-isolated-point phrasing.

2. **Via Mathlib's perfect-set machinery**: use existing results yielding an injection from Cantor
   space if available.
   - Why it might work: would give cardinality continuum directly.
   - Risk: heavier than needed if only uncountability is targeted.

### Key Difficulties

- Matching Mathlib's "perfect" predicate to the abstract theorem's hypothesis.
- Choosing the right generality (uncountable vs. cardinality $\mathfrak{c}$) for a clean statement.

### What Would a Proof Need?

- Lemma: complete (pseudo)metric space is a `BaireSpace` (Mathlib `BaireSpace` instance).
- Lemma: metric/Polish spaces are $T_1$.
- Glue: instantiate the abstract theorem; derive $\mathbb{R}$ and $2^{\mathbb{N}}$ corollaries.

## Tractability Assessment

**Difficulty**: Medium (leaning tractable)

**Justification**:
- The substantive theorem is already proven; this is instantiation + locating standard instances.
- Mathlib has rich `PolishSpace`, `BaireSpace`, and perfect-set support.
- Main risk is API-archaeology, not new mathematics.

**Estimated Effort**:
- Exploration: hours
- If tractable: days
- If hard: longer only if the abstract theorem's hypotheses need restating

## References

### Papers
- Kechris, *Classical Descriptive Set Theory* — perfect Polish spaces and Cantor–Bendixson.

### Online Resources
- Baire category theorem (Wikipedia) — complete metric ⟹ Baire.

### Mathlib
- `Topology.MetricSpace.Baire` — `BaireSpace` instance for complete spaces.
- `Topology.Perfect` — perfect sets / no isolated points.
- `Topology.MetricSpace.Polish` — `PolishSpace`.

## Metadata

```yaml
tags:
  - topology
  - baire-category
  - real-analysis
  - meagre-set
  - descriptive-set-theory
  - transcendental-numbers
related_proofs:
  - algebraic-reals-meager
difficulty: medium
source: proof-suggestion
created: 2026-06-19T17:27:54-07:00
```
