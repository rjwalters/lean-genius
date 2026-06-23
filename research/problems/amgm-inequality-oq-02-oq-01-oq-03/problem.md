# Problem: Newton–Girard $k=3$ identity $p_3 = e_1^3 - 3 e_1 e_2 + 3 e_3$ over a Finset

**Slug**: amgm-inequality-oq-02-oq-01-oq-03
**Created**: 2026-06-15
**Status**: Active
**Source**: proof-suggestion <!-- open question of gallery proof amgm-inequality-oq-02-oq-01 -->

## Problem Statement

### Formal Statement

For a finite indexed family $x_1,\dots,x_m$ with power sums
$p_k = \sum_i x_i^k$ and elementary symmetric polynomials $e_k$, prove the $k=3$
Newton–Girard identity:
$$
p_3 = e_1^3 - 3\,e_1 e_2 + 3\,e_3.
$$
The parent proof `amgm-inequality-oq-02-oq-01` establishes the $k=2$ case
($p_2 = e_1^2 - 2 e_2$) via a diagonal/off-diagonal partition of ordered pairs. The goal
is the next rung: partition ordered triples $(i,j,k)$ by coincidence pattern
(all-equal, exactly-two-equal, all-distinct).

### Plain Language

Power sums add up the cubes of a list of numbers; elementary symmetric polynomials are the
coefficients you get from multiplying out $(t-x_1)\cdots(t-x_m)$. There is a fixed algebraic
recipe converting between them. We want to prove the cube-sum case in Lean by carefully
counting how ordered triples of indices can coincide.

### Why This Matters

This is the first case where the index partition is genuinely three-way, so it stress-tests
the diagonal/off-diagonal `Finset` template and produces a reusable combinatorial lemma for
symmetric-function identities. Newton–Girard identities underpin many inequality and
resolvent arguments.

## Known Results

### What's Already Proven

- The parent proof's $k=2$ identity with the two-way pair partition.
- Mathlib has `MvPolynomial.psum`, `MvPolynomial.esymm`, and a general Newton's identity
  (`MvPolynomial.psum_eq_...` / `mul_esymm` family) — but the gallery proof works over a
  concrete `Finset` sum formulation, so the work is to match that formulation, not just cite.
- `Finset.sum_product`, `Finset.filter`, and coincidence-pattern partitions of
  `s ×ˢ s ×ˢ s`.

### What's Still Open

- The explicit $k=3$ identity in the parent proof's `Finset`-sum style (not the general
  `MvPolynomial` API).
- Clean handling of the three-way partition counts: 1 all-equal, 3 patterns of
  exactly-two-equal, and all-distinct.

### Our Goal

State and prove `p_3 = e_1^3 - 3 e_1 e_2 + 3 e_3` over a `Finset`, mirroring the parent's
diagonal/off-diagonal template, with the ordered-triple partition supplying the coefficients.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| amgm-inequality-oq-02-oq-01 | Parent: $k=2$ identity, same template | Finset pair partition |
| amgm-inequality | Root AM–GM context | symmetric polynomials |

## Initial Thoughts

### Potential Approaches

1. **Direct partition of ordered triples**: expand $e_1^3 = (\sum x_i)^3$ as a sum over
   $s\times s\times s$, group by coincidence pattern, and match against $p_3$, $e_1 e_2$,
   $e_3$ term by term.
   - Risk: the exactly-two-equal class has three sub-cases; symmetry must be exploited to
     avoid triplicated bookkeeping.

2. **Bridge to Mathlib's Newton identity**: specialize the general `MvPolynomial` result to
   the `Finset` evaluation and rewrite.
   - Risk: interfacing `MvPolynomial.esymm`/`psum` with the concrete sum may be heavier than
     the direct partition.

### Key Difficulties

- Correct multiplicities for the three-way partition.
- Keeping the proof aligned with the parent's stylistic template for reuse.

### What Would a Proof Need?

- `Finset` product/partition lemmas (`sum_product`, `filter`, cardinalities).
- The definitions of `e_1, e_2, e_3, p_3` matching the parent proof.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- A concrete, finite algebraic identity with an established $k=2$ template to follow.
- No analytic machinery; purely combinatorial `Finset` manipulation.

**Estimated Effort**:
- Exploration: hours
- If tractable: days

## References

### Mathlib
- `Mathlib/RingTheory/MvPolynomial/Symmetric/...` — `esymm`, `psum`, Newton's identities.
- `Mathlib/Algebra/BigOperators/...` — `Finset.sum_product`, partition/filter lemmas.

## Metadata

```yaml
tags:
  - combinatorics
  - symmetric-polynomials
  - newton-girard
  - algebraic-identities
  - finset
related_proofs:
  - amgm-inequality-oq-02-oq-01
  - amgm-inequality
difficulty: medium
source: proof-suggestion
created: 2026-06-15
```
