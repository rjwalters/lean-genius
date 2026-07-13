# Problem: Effective Classification of Quadratic Forms over Number Fields via Hasse–Witt Invariants

**Slug**: hilbert-11-oq-03
**Created**: 2026-07-04
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\text{Two nondegenerate quadratic forms } Q_1, Q_2 \text{ over a number field } K \text{ are equivalent}
$$
$$
\iff\ \dim Q_1 = \dim Q_2,\ \operatorname{disc} Q_1 = \operatorname{disc} Q_2,\ \text{and}\ \epsilon_v(Q_1) = \epsilon_v(Q_2)\ \forall\ \text{places } v,
$$

where $\epsilon_v$ is the Hasse–Witt invariant at place $v$ (Hasse–Minkowski). We seek an *effective* (algorithmic, formally specified) version of this classification.

### Plain Language

Hilbert's 11th problem asks for the theory of quadratic forms over algebraic number fields. The Hasse–Minkowski theorem reduces equivalence of forms over $K$ to equivalence over every completion $K_v$ (all the $p$-adic fields and the reals). The remaining classification data are: dimension, discriminant, and the Hasse–Witt invariant $\epsilon_v \in \{\pm 1\}$ at each place. We want an effective algorithm — with a precise, formalizable specification — that computes these invariants and decides equivalence, over $\mathbb{Q}$ first, then general number fields.

### Why This Matters

This is the computational heart of Hilbert's 11th problem: the local–global principle is only useful in practice with effective invariant computation. Formalizing even the $\mathbb{Q}$ case (Hilbert symbols, product formula, local invariants) would be a substantial contribution and connects to Mathlib's growing quadratic-form and local-field libraries.

## Known Results

### What's Already Proven

- Hasse–Minkowski theorem (local–global for quadratic forms over number fields) — classical; parent gallery entry `hilbert-11`.
- Mathlib has `QuadraticForm`, Witt ring basics, and `HilbertSymbol`/quadratic reciprocity fragments.
- Finiteness: only finitely many places contribute nontrivial Hasse invariants (product formula $\prod_v \epsilon_v = 1$).

### What's Still Open

- A formalized, effective decision procedure for equivalence over $\mathbb{Q}$.
- Extension to general number fields with effective place enumeration and Hasse-symbol computation.

### Our Goal

Formalize over $\mathbb{Q}$: (i) the Hasse–Witt invariant $\epsilon_p$ of a diagonal form via Hilbert symbols; (ii) the product formula $\prod_p \epsilon_p(Q) = 1$; (iii) the decision procedure `equivalent Q1 Q2 ↔ (dim, disc, all local ε agree)`. State the number-field generalization with the local-field inputs as hypotheses.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| hilbert-11 | Parent: Hasse–Minkowski / quadratic forms over number fields | local–global principle |
| hilbert-11-oq-02 | Sibling: related quadratic-form question | Witt invariants |
| quadratic-reciprocity (if present) | Hilbert symbol / reciprocity inputs | reciprocity, Legendre symbols |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Diagonalize + Hilbert symbols over ℚ**: Every form diagonalizes; compute $\epsilon_p = \prod_{i<j}(a_i, a_j)_p$ using the local Hilbert symbol, which is decidable via quadratic residues mod $p$ and 2-adic case analysis.
   - Why it might work: Hilbert symbols are elementary and computable; Mathlib has the reciprocity groundwork.
   - Risk: the prime $p=2$ and archimedean place need careful case analysis.

2. **Approach B — Number-field generalization with axiomatized local data**: State classification over $K$ taking the local invariants and place set as structured hypotheses.
   - Why it might work: cleanly separates the finished local theory from the general local-field infrastructure Mathlib lacks.
   - Risk: honest labeling as `axiomatized` for the general-field local inputs.

### Key Difficulties

- Computing Hilbert symbols at $p=2$ and at archimedean places.
- Effective enumeration of the finite set of "bad" places for general number fields.

### What Would a Proof Need?

- Key lemma 1: `HilbertSymbol` computation and its bimultiplicativity/symmetry.
- Key lemma 2: product formula $\prod_p (a,b)_p = 1$ (equivalent to quadratic reciprocity).
- Technical requirements: `Mathlib.NumberTheory.LegendreSymbol`, `Mathlib.LinearAlgebra.QuadraticForm.*`.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The $\mathbb{Q}$ case is concrete and within reach of Mathlib's reciprocity + quadratic-form tools.
- The general number-field case depends on local-field infrastructure that is only partially present, so it should be scoped as axiomatized.
- Hilbert symbols at $p=2$ are a known formalization pain point.

**Estimated Effort**:
- Exploration: 2–3 days
- If tractable (ℚ core): 1–2 weeks
- If hard (general $K$): unknown

## References

### Papers
- Serre, "A Course in Arithmetic", Ch. III–IV — Hasse–Minkowski, Hilbert symbols.
- Cassels, "Rational Quadratic Forms" — effective classification.

### Online Resources
- LMFDB quadratic-form / Hilbert-symbol pages — worked examples.

### Mathlib
- `Mathlib.NumberTheory.LegendreSymbol.Basic` — quadratic residue symbols.
- `Mathlib.LinearAlgebra.QuadraticForm.Basic` — quadratic forms, diagonalization.

## Metadata

```yaml
tags:
  - number-theory
  - quadratic-forms
  - hilbert-problems
related_proofs:
  - hilbert-11
  - hilbert-11-oq-02
difficulty: high
source: proof-suggestion
created: 2026-07-04
```

**Significance**: 7/10
**Tractability**: 4/10
