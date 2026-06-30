# Problem: Generating-Function View of Weak Compositions

**Slug**: stars-and-bars-weak-compositions-oq-01
**Created**: 2026-06-28T08:59:20-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\sum_{n \ge 0} \binom{n+k-1}{n}\, x^{n} \;=\; \frac{1}{(1-x)^{k}}, \qquad k \ge 1,
$$

equivalently, the ordinary generating function for the number of weak compositions
of $n$ into exactly $k$ parts (the number of multisets of size $n$ from $k$ types) is
$(1-x)^{-k}$, with $\binom{n+k-1}{n}$ recovered as the coefficient of $x^n$.

### Plain Language

A *weak composition* of $n$ into $k$ parts is an ordered tuple $(a_1,\dots,a_k)$ of
non-negative integers summing to $n$. Stars-and-bars counts these as
$\binom{n+k-1}{n}$. The goal is to formalize the *generating-function* proof of this
count: show the power series $\sum_n (\text{count}) x^n$ equals $(1-x)^{-k}$, and that
this is exactly the negative-binomial expansion whose coefficients are the
stars-and-bars numbers.

### Why This Matters

It connects an elementary bijective count to the analytic/algebraic machinery of
formal power series, the canonical "first nontrivial" example of the generating
function method. A clean Lean formalization gives a reusable bridge between
`Finset`-level counting and `PowerSeries`/`Polynomial` coefficient extraction in
Mathlib, useful for downstream enumerative-combinatorics formalizations.

## Known Results

### What's Already Proven

- Stars-and-bars closed form $\binom{n+k-1}{n}$ — `stars-and-bars-weak-compositions` (gallery parent).
- Negative-binomial / geometric series machinery — Mathlib `PowerSeries.invOneSubScalar`, `PowerSeries`.
- `Nat.add_choose` / `Nat.choose` identities — Mathlib.

### What's Still Open

- A formal statement that the OGF of weak-composition counts is $(1-x)^{-k}$ in `PowerSeries ℚ` (or any commutative ring).
- Extraction of $\binom{n+k-1}{n}$ as `PowerSeries.coeff n` of $(1-x)^{-k}$.

### Our Goal

Prove `coeff n ((1 - X)⁻¹)^k = (n+k-1).choose n` in `PowerSeries`, and state the OGF
identity for the weak-composition counting function defined from the parent proof.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| stars-and-bars-weak-compositions | Parent; supplies the closed-form count | bijection, `Finset.card` |
| binomial-theorem (if present) | Coefficient extraction, Pascal identities | `Nat.choose` algebra |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Direct power-series induction on $k$**: Base case $k=1$ gives
   $\sum_n x^n = (1-x)^{-1}$ (geometric series, already in Mathlib). Inductive step
   multiplies by $(1-x)^{-1}$ and uses the Vandermonde/hockey-stick identity
   $\sum_{j\le n}\binom{j+k-1}{j} = \binom{n+k}{n}$ to identify coefficients.
   - Why it might work: hockey-stick is in/near Mathlib; clean coefficient bookkeeping.
   - Risk: `PowerSeries` multiplication coefficient lemmas can be fiddly.

2. **Approach B — Identify with the negative-binomial via `PowerSeries.invOneSubPow`**:
   If Mathlib already has $(1-X)^{-k}$ coefficient lemmas, reduce to a `Nat.choose`
   rewrite.
   - Why it might work: shortest path if the lemma exists.
   - Risk: the exact lemma may not be present; may need to prove `invOneSubPow` coeff.

### Key Difficulties

- Coefficient extraction from a $k$-fold product/power in `PowerSeries`.
- Bridging the combinatorial counting function (over `Finset`) to the analytic coefficient.

### What Would a Proof Need?

- Key lemma 1: `coeff n ((1-X)⁻¹) = 1` for all $n$ (geometric series).
- Key lemma 2: hockey-stick `∑_{j≤n} (j+k-1).choose j = (n+k).choose n`.
- Technical requirements: `PowerSeries` over a commutative ring, `Nat.choose` algebra.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is elementary and the inductive structure is clear.
- Mathlib has geometric-series and `Nat.choose` infrastructure; the main work is
  coefficient bookkeeping in `PowerSeries`.
- Similar formal-power-series identities have been formalized in Mathlib.

**Estimated Effort**:
- Exploration: 1 day
- If tractable: a few days
- If hard: 1–2 weeks if `invOneSubPow` coefficients must be built from scratch

## References

### Papers
- Stanley, *Enumerative Combinatorics, Vol. 1* — §1.2 (compositions, generating functions).

### Online Resources
- Wikipedia, "Stars and bars (combinatorics)" — bijective and GF viewpoints.

### Mathlib
- `Mathlib.RingTheory.PowerSeries.Basic` — formal power series, `coeff`.
- `Mathlib.RingTheory.PowerSeries.WellKnown` — `invOneSubScalar` / geometric series.
- `Mathlib.Combinatorics` / `Nat.choose` — binomial coefficient identities.

## Metadata

```yaml
tags:
  - combinatorics
  - enumerative-combinatorics
  - generating-functions
  - stars-and-bars
  - binomial-coefficients
related_proofs:
  - stars-and-bars-weak-compositions
difficulty: medium
source: gallery-gap
created: 2026-06-28T08:59:20-07:00
```
