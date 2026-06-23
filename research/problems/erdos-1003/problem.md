# Problem: Consecutive k-Equal Totients

**Slug**: erdos-1003-oq-02
**Created**: 2026-03-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall k \geq 1, \; |\{n \in \mathbb{N} : \varphi(n) = \varphi(n+1) = \cdots = \varphi(n+k)\}| = \infty
$$

Erdos conjectured that for every $k \geq 1$, there are infinitely many $n$ with $k+1$ consecutive equal values of Euler's totient function.

### Plain Language

The parent proof (erdos-1003) addresses the case $k=1$: are there infinitely many $n$ with $\varphi(n) = \varphi(n+1)$? This extension asks: for any fixed $k$, can we always find arbitrarily long runs of consecutive integers with the same totient value?

### Why This Matters

- Strengthening of a classic Erdos conjecture about the totient function
- Connects to the distribution and concentration of totient values
- The k=1 case is already formalized; the generalization tests whether the proof technique extends

## Known Results

### What's Already Proven

- `erdos-1003` — Base conjecture formalized (axiomatized, 5 axioms, 261 lines)
- Ford, Luca, Pomerance (2010): proved the k=1 case unconditionally
- Goldston, Graham, Pintz, Yildirim: related work on gaps in totient values

### What's Still Open

- General k case: no unconditional proof known for arbitrary k
- Best partial results: k=1 proved, k=2 widely believed, larger k open

### Our Goal

Formalize the statement for general k and axiomatize the known partial results. If the proof technique from k=1 (Ford-Luca-Pomerance) can be stated to generalize, capture that structure.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1003 | Parent proof, k=1 case | Totient function axioms, consecutive values |
| euler-totient | Euler's totient properties | Nat.totient, multiplicativity |

## Initial Thoughts

### Potential Approaches

1. **Axiomatize the general statement**: Define `ConsecutiveKEqualTotients(k)` and state infinitude
   - Why it might work: Clean extension of existing axiom structure
   - Risk: May be too shallow without proof content

2. **Formalize Ford-Luca-Pomerance technique structure**: Capture the sieve-theoretic argument skeleton
   - Why it might work: Gives the proof architecture even if details are axiomatized
   - Risk: Sieve methods are complex to formalize

### Key Difficulties

- The k=1 proof uses deep sieve theory not available in Mathlib
- Generalizing to arbitrary k requires understanding concentration of totient values

### What Would a Proof Need?

- Definition: `ConsecutiveKEqualTotients(k, n)` predicate
- Key lemma: density/infinitude for k=1 implies structure for general k
- Axioms for sieve-theoretic ingredients if full proof is out of reach

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- Statement formalization is straightforward
- Proof content requires sieve theory beyond current Mathlib
- But axiomatized approach following erdos-1003 pattern is feasible

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable (axiomatized): 3-5 days

## References

### Papers
- Ford, Luca, Pomerance (2010) — "Coincidences in the values of the Euler function"
- Erdos (1935) — Original conjecture on consecutive equal totients

### Mathlib
- `Mathlib.Data.Nat.Totient` — Euler's totient function
- `Mathlib.NumberTheory.ArithmeticFunction` — Arithmetic function infrastructure

## Metadata

```yaml
tags:
  - erdos
  - number-theory
  - totient-function
  - consecutive-values
related_proofs:
  - erdos-1003
  - euler-totient
difficulty: medium-high
source: gallery-gap
created: 2026-03-30
```
