# Problem: Vahlen–Capelli Irreducibility of Xⁿ − a over ℚ

**Slug**: cube-root-3-irrational-oq-02-oq-03
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a field $K$ and $a \in K^\times$, the binomial $X^n - a$ is irreducible over $K$ iff

$$
a \notin K^p \ \text{for every prime } p \mid n, \quad\text{and}\quad \bigl(4 \mid n \implies a \notin -4K^4\bigr).
$$

### Plain Language

The gallery proof `cube-root-3-irrational-oq-02` shows $\sqrt[3]{3}$ is irrational by proving $X^3 - 3$ is irreducible over $\mathbb{Q}$ via Eisenstein. This problem asks for the full classical converse/criterion: exactly when is $X^n - a$ irreducible? The clean answer is the **Vahlen–Capelli theorem** (Lang, *Algebra*, VI.9.1). Half is trivial (a perfect $n$-th power gives a rational root), but the complete criterion — including the delicate $4 \mid n$ exceptional case involving $-4K^4$ — is the substantive content.

### Why This Matters

The criterion is the definitive statement on irreducibility of pure binomials, underpinning radical extensions, Kummer theory, and cyclotomic constructions. Mathlib has Eisenstein and some cyclotomic irreducibility but, as far as is known, no general Vahlen–Capelli binomial criterion — a genuine formalization gap.

## Known Results

### What's Already Proven
- Eisenstein's criterion — `Polynomial.irreducible_of_eisenstein_criterion` (Mathlib).
- $X^3 - 3$ irreducible over $\mathbb{Q}$ — gallery `cube-root-3-irrational-oq-02`.
- Cyclotomic polynomial irreducibility — Mathlib `Polynomial.cyclotomic`.

### What's Still Open (for formalization)
- The general Vahlen–Capelli criterion for arbitrary $n$ and field $K$.
- The $4 \mid n$ exceptional clause ($a \notin -4K^4$).

### Our Goal
Formalize the criterion, at minimum over $\mathbb{Q}$ and for $n$ not divisible by 4 (the clean case: $X^n - a$ irreducible iff $a$ is not a $p$-th power for any prime $p \mid n$). Then attempt the $4 \mid n$ refinement.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cube-root-3-irrational-oq-02 | Direct parent; $n=3$ special case | Eisenstein |
| abel-ruffini-galois-extensions | Radical extensions, splitting fields | Galois theory |

## Initial Thoughts

### Potential Approaches
1. **Prime-power reduction**: reduce to $n = p^k$ via multiplicativity of the criterion, then handle prime and prime-power cases. Standard textbook route.
2. **Field-norm / Kummer-theoretic**: use that $[K(\alpha):K] = n$ iff the relevant power conditions hold, connecting to the structure of $K^\times / (K^\times)^n$.

### Key Difficulties
- The $-4K^4$ exceptional case (e.g. $X^4 + 4 = (X^2-2X+2)(X^2+2X+2)$) must be handled explicitly.
- Managing arbitrary base fields vs specializing to $\mathbb{Q}$.

### What Would a Proof Need?
- Lemma: if $a$ is not a $p$-th power for any $p \mid n$ (and the 4-clause holds), then $[K(\sqrt[n]{a}):K] = n$.
- Multiplicativity/reduction to prime-power $n$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**: Classical, fully-understood mathematics with a known clean proof; the clean ($4 \nmid n$) case is a reasonable Lean target. The 4-clause adds real but bounded difficulty.

## References

### Papers / Texts
- S. Lang, *Algebra*, Theorem VI.9.1 (Vahlen–Capelli).// Karpilovsky, *Topics in Field Theory*.

### Mathlib
- `Polynomial.irreducible_of_eisenstein_criterion`, `Polynomial.cyclotomic`, `Algebra.adjoin`, `IsSplittingField`.

## Metadata

```yaml
tags:
  - number-theory
  - field-theory
  - polynomial-irreducibility
  - vahlen-capelli
related_proofs:
  - cube-root-3-irrational-oq-02
  - abel-ruffini-galois-extensions
difficulty: medium
source: gallery-gap
created: 2026-07-04
```
