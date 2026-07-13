# Problem: Schreier Refinement Theorem and the Zassenhaus Butterfly Lemma

**Slug**: abel-ruffini-galois-extensions-oq-04-oq-03
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

**Zassenhaus (butterfly) lemma.** Let $A \trianglelefteq A^\ast$ and $B \trianglelefteq B^\ast$ be subgroups of a group $G$. Then
$$
\frac{A\,(A^\ast \cap B^\ast)}{A\,(A^\ast \cap B)} \;\cong\; \frac{B\,(B^\ast \cap A^\ast)}{B\,(B^\ast \cap A)} .
$$

**Schreier refinement theorem.** Any two subnormal (normal) series of a group admit equivalent refinements: there exist refinements with the same multiset of factor groups up to isomorphism.

### Plain Language

The parent entry formalizes Jordan–Hölder uniqueness via Mathlib's `JordanHolderLattice`. The standard textbook route to Jordan–Hölder goes through Schreier refinement, which in turn rests on the Zassenhaus butterfly lemma. Neither Schreier refinement nor the Zassenhaus lemma is currently in Mathlib. This problem asks to formalize them, giving a self-contained derivation of comparability of composition series that does not merely reuse Mathlib's abstract lattice-theoretic Jordan–Hölder.

### Why This Matters

The Zassenhaus lemma and Schreier refinement are foundational group theory taught in every first algebra course, yet absent from Mathlib. Adding them fills a genuine library gap, provides an independent second proof route to Jordan–Hölder, and supplies reusable machinery for module composition series and the general theory of subnormal series.

## Known Results

### What's Already Proven

- Jordan–Hölder uniqueness through the abstract lattice interface — parent `abel-ruffini-galois-extensions-oq-04` and Mathlib's `CompositionSeries.jordan_holder`.
- Second and third isomorphism theorems for groups — `Mathlib.GroupTheory.QuotientGroup`.
- The `JordanHolderLattice` typeclass and its consequences.

### What's Still Open

- The Zassenhaus butterfly lemma as a named, reusable Mathlib-style theorem.
- The Schreier refinement theorem for (sub)normal series.
- A Jordan–Hölder derivation via Schreier that is logically independent of the existing lattice proof.

### Our Goal

Formalize the Zassenhaus lemma for subgroups with the stated isomorphism, then use it to prove Schreier refinement, and (stretch) re-derive comparability of composition series without invoking `JordanHolderLattice`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| abel-ruffini-galois-extensions-oq-04 | Parent: Jordan–Hölder via lattice | `JordanHolderLattice`, composition series |
| abel-ruffini-galois-extensions-oq-03-oq-01 | Solvability / normal series context | subnormal series, solvable groups |

## Initial Thoughts

### Potential Approaches

1. **Approach A — isomorphism-theorem assembly**: Build the butterfly lemma directly from the second isomorphism theorem applied twice to the products $A(A^\ast \cap B^\ast)$ and $B(B^\ast \cap A^\ast)$, exhibiting both quotients as $(A^\ast \cap B^\ast)/\bigl((A^\ast \cap B)(A \cap B^\ast)\bigr)$.
   - Why it might work: the classical proof reduces the whole lemma to one common middle quotient via the second isomorphism theorem, all of which Mathlib has.
   - Risk: the normality bookkeeping ($A \trianglelefteq A^\ast$ giving $A^\ast \cap B \trianglelefteq A^\ast \cap B^\ast$, etc.) is fiddly and Mathlib's `Subgroup.normal` lemmas may not cover every intersection/product needed.

2. **Approach B — refinement first, lemma as a black box**: State Schreier refinement, insert Zassenhaus as the key inductive step, and prove Zassenhaus only in the form actually consumed.
   - Why it might work: minimizes the surface of the butterfly lemma to what is needed.
   - Risk: harder to reuse; still needs the core isomorphism.

### Key Difficulties

- Establishing all the normality relations among products and intersections of the four subgroups.
- Managing Mathlib's `Subgroup` product (`Subgroup.mul` / `⊔`) versus set-product `A * B` and their normality lemmas.
- Bookkeeping the "equivalent refinement" as a multiset/permutation of factor isomorphisms.

### What Would a Proof Need?

- Key lemma 1: normality of $A(A^\ast \cap B) \trianglelefteq A(A^\ast \cap B^\ast)$ and its mirror.
- Key lemma 2: both butterfly quotients isomorphic to the common middle quotient (double application of the second isomorphism theorem).
- Technical requirements: `QuotientGroup.quotientMulEquivOfEq`, second isomorphism theorem, `Subgroup.normal_comap`/product-normality lemmas.

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- The core isomorphism is standard and every ingredient (isomorphism theorems, subgroup products) exists in Mathlib.
- The difficulty is entirely in normality bookkeeping and product/intersection subgroup manipulation, which is notoriously verbose in Lean.
- No comparable formalization exists yet, so there is no template to copy.

**Estimated Effort**:
- Exploration: 2–3 days to nail down the subgroup product/normality API.
- If tractable: 1–2 weeks for the butterfly lemma; Schreier refinement adds more.
- If hard: the multiset-of-factors equivalence could be a substantial separate effort.

## References

### Papers
- Zassenhaus, "Zum Satz von Jordan-Hölder-Schreier", *Abh. Math. Sem. Univ. Hamburg* 10 (1934).
- Lang, *Algebra* (3rd ed.), Chapter I — butterfly lemma and Schreier refinement.

### Online Resources
- https://leanprover-community.github.io/mathlib4_docs/ — `QuotientGroup`, `Subgroup`, `CompositionSeries`.

### Mathlib
- `Mathlib.GroupTheory.QuotientGroup` — isomorphism theorems.
- `Mathlib.Order.JordanHolder` — `JordanHolderLattice`, `CompositionSeries.jordan_holder`.
- `Mathlib.GroupTheory.Subgroup.Basic` — subgroup products and normality.

## Metadata

```yaml
tags:
  - group-theory
  - jordan-holder
  - composition-series
  - zassenhaus-lemma
  - schreier-refinement
  - abel-ruffini
related_proofs:
  - abel-ruffini-galois-extensions-oq-04
  - abel-ruffini-galois-extensions-oq-03-oq-01
difficulty: high
source: gallery-gap
created: 2026-07-04
```
