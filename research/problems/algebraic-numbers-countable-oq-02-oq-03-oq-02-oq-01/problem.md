# Problem: Dense Countable Sets are Fσ but not Gδ in Perfect Polish Spaces

**Slug**: algebraic-numbers-countable-oq-02-oq-03-oq-02-oq-01
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall\, X \text{ a perfect Polish space},\ \forall\, D \subseteq X \text{ countable and dense}:\quad D \in \mathbf{\Sigma}^0_2 \ \wedge\ D \notin \mathbf{\Pi}^0_2 .
$$

Equivalently, every dense countable subset of a nonempty perfect Polish space is $F_\sigma$ (a countable union of closed sets) but not $G_\delta$ (a countable intersection of open sets).

### Plain Language

The parent entry shows that the algebraic reals are $F_\sigma$ but not $G_\delta$, while the transcendental reals form a dense $G_\delta$. That proof rests on Baire category: a dense $G_\delta$ set is "large", and a dense countable set cannot also be $G_\delta$ or its complement (also dense $G_\delta$) would meet it, contradicting Baire. This problem abstracts the argument once and for all: replace "algebraic reals in $\mathbb{R}$" by "any countable dense set in any perfect Polish space", recovering the $\mathbb{Q} \subseteq \mathbb{R}$ and algebraic-reals cases as instances.

### Why This Matters

This is the natural home for a family of scattered results. A single abstract theorem yields, as corollaries: $\mathbb{Q}$ is not $G_\delta$ in $\mathbb{R}$; the algebraic reals are not $G_\delta$; any countable dense subset of $\mathbb{R}^n$, Cantor space, or Baire space is not $G_\delta$. It is a clean, citable descriptive-set-theory lemma and removes duplication across gallery entries.

## Known Results

### What's Already Proven

- `algebraicReals_not_isGδ` — the concrete algebraic-reals case (parent `algebraic-numbers-countable-oq-02-oq-03-oq-02`).
- The transcendental reals are a dense $G_\delta$ (sibling entry).
- Baire category theorem for complete metric / Polish spaces — `Mathlib.Topology.Baire`.
- A countable set with no isolated points-hypothesis fails to be $G_\delta$ in a Baire space where singletons are nowhere dense.

### What's Still Open

- The uniform statement quantified over all perfect Polish spaces and all countable dense subsets.
- The clean packaging so `ℚ ⊆ ℝ`, algebraic reals, and Cantor/Baire space are one-line instances.

### Our Goal

State and prove `denseCountable_isFσ_not_isGδ`: in a nonempty perfect Polish space, a countable dense set is $F_\sigma$ and not $G_\delta$, then re-derive the parent's `algebraicReals_not_isGδ` from it.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| algebraic-numbers-countable-oq-02-oq-03-oq-02 | Direct parent (concrete case) | Baire category, $G_\delta$ complement |
| algebraic-numbers-countable-oq-02-oq-03 | Transcendental reals dense $G_\delta$ | dense $G_\delta$, comeager sets |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Baire via the complement**: A countable set $D$ is $F_\sigma$ (union of its singletons, each closed in a $T_1$ space). If $D$ were also $G_\delta$, then in a perfect space each singleton is nowhere dense, so $D$ is meager; but a dense $G_\delta$ is comeager, and meager + comeager forces the whole space to be meager, contradicting Baire.
   - Why it might work: exactly the parent's argument, only the ambient space is generalized.
   - Risk: need the perfectness hypothesis (no isolated points) to guarantee singletons are nowhere dense.

2. **Approach B — direct nowhere-dense intersection**: Show $D$ dense $G_\delta$ and its dense $G_\delta$ complement would be disjoint dense comeager sets, impossible in a Baire space.
   - Why it might work: symmetric and short.
   - Risk: constructing the complement's $G_\delta$ structure requires $D$ countable, needs care.

### Key Difficulties

- Correctly capturing "perfect" (`Perfect` / no isolated points) so singletons are nowhere dense.
- Choosing Mathlib's spelling of $F_\sigma$ / $G_\delta$ (`IsGδ`, `IsFsigma` if present, or via `residual`/`meager`).

### What Would a Proof Need?

- Key lemma 1: in a perfect $T_1$ space, every singleton is nowhere dense, hence a countable set is meager.
- Key lemma 2: a dense $G_\delta$ in a Baire space is comeager; a meager comeager set is empty-complemented, contradiction.
- Technical requirements: `Perfect`, `IsGδ`, `meager`/`residual`, Baire category API.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical content is already validated in the concrete parent case.
- The work is abstraction: identifying the minimal hypotheses (perfect Polish, or perfect + Baire + $T_1$) and threading Mathlib's `IsGδ`/`meager` lemmas.
- Mathlib already has strong Baire-category infrastructure.

**Estimated Effort**:
- Exploration: 1 day to survey `IsGδ` / `meager` / `Perfect` API.
- If tractable: 2–4 days including re-deriving the parent as a corollary.
- If hard: only if the $F_\sigma$ side lacks direct Mathlib support.

## References

### Papers
- Kechris, *Classical Descriptive Set Theory* (1995), Section 8 — Borel hierarchy, Baire category, perfect Polish spaces.

### Online Resources
- https://leanprover-community.github.io/mathlib4_docs/ — `IsGδ`, `Perfect`, `residual`, `meager`.

### Mathlib
- `Mathlib.Topology.Baire` — Baire category theorem.
- `Mathlib.Topology.GDelta` — `IsGδ` API.
- `Mathlib.Topology.Perfect` — perfect sets / no isolated points.

## Metadata

```yaml
tags:
  - topology
  - baire-category
  - descriptive-set-theory
  - gdelta-set
  - borel-hierarchy
  - real-analysis
related_proofs:
  - algebraic-numbers-countable-oq-02-oq-03-oq-02
  - algebraic-numbers-countable-oq-02-oq-03
difficulty: medium
source: gallery-gap
created: 2026-07-04
```
