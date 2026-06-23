# Problem: Factorization Bound via Kummer's Theorem

**Slug**: chebyshev-pnt-bridge-oq-01
**Created**: 2026-04-12
**Status**: Active
**Source**: gallery-extension

## Problem Statement

### Formal Statement

For all primes p and natural numbers n ≥ 1:

$$
p^{v_p\binom{2n}{n}} \leq 2n
$$

where $v_p(m)$ denotes the p-adic valuation of m.

### Plain Language

The largest power of any prime p dividing the central binomial coefficient C(2n, n) is at most 2n. This bound is a key ingredient in Chebyshev's approach to the Prime Number Theorem, used to bound the prime-counting function π(x).

### Why This Matters

The existing `chebyshev-pnt-bridge` proof has 2 sorries remaining, and this factorization bound is central to the argument. Proving it would make progress toward a fully verified Chebyshev–PNT bridge. Kummer's theorem (the number of carries in base-p addition determines the p-adic valuation of binomial coefficients) provides the cleanest path.

## Known Results

### What's Already Proven

- `ChebyshevPNTBridge.lean` has 10 theorems, 2 definitions, 2 sorries remaining
- Imports `Mathlib.Data.Nat.Choose.Factorization` — Kummer's theorem infrastructure
- Imports `Mathlib.NumberTheory.Primorial` for primorial bounds

### What's Still Open

- The factorization bound p^{v_p(C(2n,n))} ≤ 2n
- May also need: Legendre's formula v_p(n!) = Σ_{k≥1} ⌊n/p^k⌋

### Our Goal

Prove the factorization bound using Kummer's theorem and related results from Mathlib's `Nat.Choose.Factorization` module.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| chebyshev-pnt-bridge | Direct source — fills sorry | Chebyshev bounds, prime counting |
| infinitude-of-primes | Related number theory | Prime properties |
| prime-gap-bounds | Related analytic number theory | Prime distribution |

## Initial Thoughts

### Potential Approaches

1. **Via Kummer's theorem**: v_p(C(2n,n)) = number of carries when adding n+n in base p. Since carries happen in at most log_p(2n) positions, and each carry contributes 1, we get v_p(C(2n,n)) ≤ log_p(2n), hence p^{v_p(C(2n,n))} ≤ 2n.
   - Why it might work: Mathlib has `Nat.Choose.Factorization` with Kummer's infrastructure
   - Risk: May need to build the carry-counting argument

2. **Via Legendre's formula**: v_p(C(2n,n)) = v_p((2n)!) - 2·v_p(n!) = Σ_k (⌊2n/p^k⌋ - 2⌊n/p^k⌋). Each term is 0 or 1, and terms vanish for p^k > 2n.
   - Why it might work: More elementary, uses floor function properties
   - Risk: Summing over k requires careful bound on number of terms

### Key Difficulties

- Connecting Kummer's theorem to the prime power bound
- Managing p-adic valuation arithmetic in Lean
- Ensuring all Mathlib lemmas are compatible

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Both approaches are well-known classical results
- Mathlib has dedicated `Nat.Choose.Factorization` module
- The proof is short on paper (few lines)
- Source file already imports the right Mathlib modules

## Metadata

```yaml
tags:
  - number-theory
  - analytic-number-theory
  - prime-counting
  - chebyshev-bounds
related_proofs:
  - chebyshev-pnt-bridge
  - infinitude-of-primes
difficulty: medium
source: gallery-extension
created: 2026-04-12
```
