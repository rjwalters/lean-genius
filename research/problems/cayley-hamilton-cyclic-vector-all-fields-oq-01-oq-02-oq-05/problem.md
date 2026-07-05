# Problem: Multi-block rational canonical form via the K[X]-module structure theorem

**Slug**: cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02-oq-05
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall\, K \text{ a field},\ \forall\, A \in M_n(K),\quad
A \sim \bigoplus_{i=1}^{r} C(p_i),\qquad p_1 \mid p_2 \mid \cdots \mid p_r,
$$
where each $C(p_i)$ is the companion matrix of an invariant factor $p_i \in K[X]$ and
$\prod_i p_i$ is the characteristic polynomial. Equivalently: every finitely generated
torsion $K[X]$-module decomposes as $\bigoplus_i K[X]/(p_i)$ with $p_1\mid\cdots\mid p_r$,
and this yields the rational canonical form (RCF) of $A$.

### Plain Language

The parent gallery proof shows a **nonderogatory** (single-cyclic-vector) matrix is
similar to the companion matrix of its characteristic polynomial — the single-block
case. This problem removes the nonderogatory hypothesis: *every* square matrix over
*any* field is similar to a direct sum of companion blocks (its rational canonical
form). The natural route is the structure theorem for finitely generated modules over
the PID $K[X]$, viewing $K^n$ as a $K[X]$-module via $A$.

### Why This Matters

RCF is a cornerstone of linear algebra and is currently a **Mathlib gap**: Mathlib has
the module structure theorem over PIDs but does not package the general matrix RCF /
similarity-to-block-companion form. Delivering it is a substantial, genuinely useful
upstream contribution, with the single-block scaffold already in the gallery.

## Known Results

### What's Already Proven

- Single-block case: nonderogatory $A$ is similar to $C(\chi_A)$ — gallery proof
  `cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02`.
- Structure theorem for f.g. modules over a PID — available in Mathlib
  (`Mathlib.Algebra.Module.PID`, invariant factors / `Module.equiv_directSum_...`).
- Cayley–Hamilton over commutative rings — Mathlib `Matrix.aeval_self_charpoly`.

### What's Still Open

- Packaging the $K[X]$-module decomposition of $K^n$ into a similarity statement
  $A \sim \bigoplus C(p_i)$ with an explicit change-of-basis matrix.
- Uniqueness of invariant factors as a similarity invariant (RCF canonicality).

### Our Goal

Formalize: for any field $K$ and $A \in M_n(K)$, $A$ is similar to the direct sum of
companion matrices of its invariant factors, using the PID structure theorem with the
single-block companion result as the per-summand scaffold.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02 | Single-block scaffold | cyclic vector, Krylov matrix, companion similarity |
| cayley-hamilton | Cayley–Hamilton over general rings | adjugate/charpoly identities |

## Initial Thoughts

### Potential Approaches

1. **Approach A — module structure theorem transport**:
   Give $K^n$ the $K[X]$-module structure $p \cdot v = p(A)v$; apply Mathlib's PID
   invariant-factor decomposition; each cyclic summand $K[X]/(p_i)$ gives a companion
   block via the single-block result.
   - Why it might work: reuses existing Mathlib PID machinery + the scaffold lemma.
   - Risk: translating an abstract module iso into an explicit matrix similarity
     (basis assembly, block-diagonal change of basis).

2. **Approach B — direct invariant-factor computation via Smith normal form**:
   Compute the Smith normal form of $XI - A$ over $K[X]$; its nontrivial diagonal
   entries are the invariant factors.
   - Why it might work: constructive, avoids abstract module transport.
   - Risk: Smith normal form over $K[X]$ may itself be a partial Mathlib gap.

### Key Difficulties

- Bridging the abstract module isomorphism to a concrete `Matrix.SimilarTo` statement.
- Block-diagonal basis assembly and index bookkeeping across summands.

### What Would a Proof Need?

- Key lemma 1: the $A$-module structure on $K^n$ is f.g. torsion over $K[X]$.
- Key lemma 2: each invariant-factor summand $K[X]/(p_i)$ is $A$-cyclic ⇒ companion block.
- Technical requirements: explicit change-of-basis extraction from the module iso.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Mathlib supplies the PID structure theorem, but packaging RCF as matrix similarity
  is nontrivial and currently missing upstream.
- The single-block scaffold reduces per-summand risk substantially.
- Explicit basis/similarity extraction is the main formalization overhead.

**Estimated Effort**:
- Exploration: 2–4 days mapping Mathlib PID API to the matrix setting
- If tractable: multiple weeks (Mathlib-PR-scale)
- If hard: Smith-normal-form gaps could extend it

## References

### Papers
- Dummit & Foote, *Abstract Algebra*, Ch. 12 — rational canonical form via PID modules.

### Online Resources
- Mathlib `Module.PID` docs — invariant factors and cyclic decomposition.

### Mathlib
- `Mathlib.Algebra.Module.PID` — structure theorem for f.g. modules over a PID.
- `Matrix.charpoly`, `Matrix.companion` (if present) — companion-matrix API.
- `LinearMap.toMatrix` — basis change-of-coordinates for the similarity statement.

## Metadata

```yaml
tags:
  - linear-algebra
  - rational-canonical-form
  - module-theory
  - cayley-hamilton
  - mathlib-gap
related_proofs:
  - cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02
  - cayley-hamilton
difficulty: high
source: gallery-gap
created: 2026-07-04
```
