# Problem: Elementary lower bound on k-th prime ≡ 3 (mod 4) vs PNT asymptotic

**Slug**: dirichlets-theorem-oq-02-oq-03
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The Euclid-style construction `N = 4·(n+1)! − 1` (and the product variant
`N = 4·p₁⋯p_k − 1` over known primes `≡ 3 (mod 4)`) certifies a prime `≡ 3 (mod 4)`
exceeding `n`. Question: what lower bound on the `k`-th prime `p_k ≡ 3 (mod 4)` do these
elementary constructions certify, and how does it compare with the true asymptotic
`p_k \sim 2k\ln k` from the PNT for arithmetic progressions?

### Plain Language

The parent `dirichlets-theorem-oq-02` proves infinitely many primes `≡ 3 (mod 4)` by an
Euclid-style factorial/product construction. Each step produces a new such prime, so it
yields a (very weak) explicit growth bound on the `k`-th such prime. This OQ asks to
state that certified lower bound and contrast it with the genuine `~2k ln k` asymptotic.

### Why This Matters

Quantifies exactly how far the elementary Euclid argument is from the truth — a concrete,
formalizable statement about the gap between constructive lower bounds and analytic
asymptotics, in the same spirit as the shipped Bertrand/Dirichlet OQ-extensions.

## Known Results

### What's Already Proven

- Parent `dirichlets-theorem-oq-02`: infinitude of primes `≡ 3 (mod 4)` via the
  `4·(n+1)! − 1` / product construction.
- The PNT for arithmetic progressions gives `π(x; 4, 3) \sim x/(2\ln x)`, hence
  `p_k \sim 2k\ln k` (analytic, likely out of scope to formalize here).

### Our Goal

Formalize the **certified** lower bound the construction yields for `p_k` (e.g. a
factorial-type or doubly-exponential bound) as a clean Lean statement; contrast the
`~2k ln k` truth in prose. The tractable deliverable is the elementary certified bound.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| dirichlets-theorem-oq-02 | parent; the construction being quantified | Euclid-style prime construction |
| bertrands-postulate-oq-05-oq-02 | sibling explicit prime-bound OQ-extension | Legendre / factorial valuations |

## Initial Thoughts

### Potential Approaches

1. **Recurrence bound**: track the size of `N` at each construction step to get an
   explicit (fast-growing) upper bound on `p_k`, giving a certified lower bound on the
   count below `x`.
   - Risk: bound is very weak; keep the statement honest (upper bound on `p_k`, not tight).

## Tractability Assessment

**Difficulty**: Medium

**Justification**: The constructive side is elementary and in reach; the asymptotic side
is analytic and should stay as context, not a formalized target. Scope to the certified
elementary bound to keep it tractable and honest.

## References

### Mathlib
- `Nat.Prime`, `Nat.factorial`, modular arithmetic lemmas; parent entry's Lean file.

## Metadata

```yaml
tags:
  - number-theory
  - primes
  - dirichlet
  - arithmetic-progressions
related_proofs:
  - dirichlets-theorem-oq-02
difficulty: medium
source: gallery-gap
created: 2026-07-01
```

**Significance**: 6/10
**Tractability**: 6/10
