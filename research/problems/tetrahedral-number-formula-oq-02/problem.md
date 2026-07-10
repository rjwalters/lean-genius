# Problem: Uniform Cleared-Denominator Polynomial Form for Higher-Dimensional Figurate Sums

**Slug**: tetrahedral-number-formula-oq-02
**Created**: 2026-07-09
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\sum_{k=0}^{n} \binom{k+d-1}{d} = \binom{n+d}{d+1}
\qquad\text{(hockey-stick identity, dimension } d)
$$

The question is whether the **cleared-denominator polynomial form** of this
identity — i.e. writing $\binom{n+d}{d+1}$ as
$\tfrac{1}{(d+1)!}\prod_{j=0}^{d}(n+j)$ and proving the equality with
denominators multiplied out — can be produced **uniformly in $d$** by a single
Lean argument, rather than a separate per-dimension proof:

$$
(d+1)! \cdot \sum_{k=0}^{n} \binom{k+d-1}{d} \;=\; \prod_{j=1}^{d+1}(n+j-1) \cdot \frac{(d+1)!}{(d+1)!}.
$$

### Plain Language

The base gallery proof (`tetrahedral-number-formula`) shows that summing the
first $n$ triangular numbers gives the $n$-th tetrahedral number,
$\sum \binom{k+1}{2} = \binom{n+2}{3}$ — the $d=2$ case. Its open question asks
whether the polynomial identity, once you clear the denominator $d!$, follows
from one uniform argument for *every* dimension $d$, or whether the growing
factorial denominator forces a fresh parity/divisibility argument at each $d$.

### Why This Matters

A single dimension-generic proof would give a clean, reusable
`Finset.sum`-over-binomials lemma parameterized by $d$, subsuming the
triangular ($d=1$), tetrahedral ($d=2$), pentatope ($d=3$), and all higher
figurate-number summation identities. It is also a good test of whether
Mathlib's `Nat.choose` / `Nat.factorial` API supports denominator-clearing
proofs generically or only case-by-case.

## Known Results

### What's Already Proven

- `tetrahedral-number-formula` (gallery) — the $d=2$ instance $\sum_{k}\binom{k+1}{2} = \binom{n+2}{3}$, machine-checked.
- `Nat.sum_range_choose_mul_pow` and the hockey-stick identity `Nat.sum_Icc_choose` in Mathlib — the general telescoping form over `Nat.choose`.
- `Nat.choose_mul_factorial_le` / `Nat.factorial_mul_factorial_dvd_factorial` — divisibility infrastructure for cleared-denominator arguments.

### What's Still Open

- Whether a single Lean term, generic in $d$, proves the cleared-denominator polynomial form for all $d$.
- Whether the $d!$ denominator obstructs a uniform proof (requiring per-$d$ parity/divisibility lemmas) or whether `Nat.choose`'s built-in divisibility handles it uniformly.

### Our Goal

Prove the hockey-stick identity in its cleared-denominator polynomial form
uniformly in $d$ (a single `theorem` quantified over `d : ℕ`), or, failing
that, precisely characterize the obstruction that forces a per-dimension
argument.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| tetrahedral-number-formula | Parent proof; the $d=2$ special case | `Finset.sum`, `Nat.choose`, induction |
| sum-of-kth-powers | Companion figurate/power-sum summation identities | Euler-Maclaurin, polynomial closed forms |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Generic hockey-stick via `Nat.sum_Icc_choose`**: Prove the
   binomial form $\sum \binom{k+d-1}{d} = \binom{n+d}{d+1}$ from Mathlib's
   hockey-stick lemma, then multiply both sides by $(d+1)!$ and rewrite
   $\binom{n+d}{d+1}\,(d+1)! = \prod_{j}(n+j)$ using `Nat.choose_mul_factorial`.
   - Why it might work: keeps everything over `Nat.choose`, whose divisibility is definitional; the denominator never actually appears.
   - Risk: expressing the falling/rising product $\prod_{j=1}^{d+1}(n+j-1)$ generically may need a custom `Finset.prod` lemma.

2. **Approach B — Induction on $d$**: Base case $d=1$ (triangular), inductive
   step reducing dimension $d+1$ to $d$ via Pascal's rule.
   - Why it might work: mirrors the geometric "stacking" intuition.
   - Risk: the inductive step mixes the sum index $n$ and the dimension $d$; bookkeeping may be heavy.

### Key Difficulties

- Expressing the cleared-denominator product $\prod_{j=1}^{d+1}(n+j-1)$ as a Lean term generic in $d$.
- Deciding whether to work over `ℕ` (divisibility definitional but subtraction awkward) or `ℚ` (division clean but needs cast management).

### What Would a Proof Need?

- Key lemma 1: generic hockey-stick $\sum_{k=0}^{n}\binom{k+d-1}{d} = \binom{n+d}{d+1}$ (likely `Nat.sum_Icc_choose` reindexed).
- Key lemma 2: $\binom{m}{r}\cdot r! \cdot (m-r)! = m!$ specialized to clear the denominator without leaving `ℕ`.
- Technical requirements: `Nat.choose`, `Nat.factorial`, `Finset.prod_range`, careful cast lemmas if `ℚ` is used.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The binomial identity itself is standard and in Mathlib; the novelty is the *uniform-in-$d$* cleared-denominator form.
- Similar denominator-clearing arguments (e.g. Faulhaber-style power sums) have been formalized, suggesting the API is adequate.
- Main uncertainty is packaging the general product cleanly, not the underlying mathematics.

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: 3-5 days
- If hard: 1-2 weeks (if per-dimension parity arguments prove unavoidable)

## References

### Papers
- Conway & Guy, *The Book of Numbers* (1996) — figurate numbers and the hockey-stick identity.

### Online Resources
- https://en.wikipedia.org/wiki/Hockey_stick_identity — statement and combinatorial proof.

### Mathlib
- `Mathlib.Combinatorics.Choose.Sum` — `Nat.sum_Icc_choose` and related hockey-stick lemmas.
- `Mathlib.Data.Nat.Choose.Factorization` — divisibility of binomial coefficients for denominator clearing.

## Metadata

```yaml
tags:
  - combinatorics
  - algebra
  - figurate-numbers
related_proofs:
  - tetrahedral-number-formula
  - sum-of-kth-powers
difficulty: medium
source: gallery-gap
created: 2026-07-09
```
