# Problem: Erdős #307: Prime Reciprocal Products — Complete Proof

**Slug**: erdos-307-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\nexists \text{ finite prime sets } P, Q \text{ s.t. } \left(\sum_{p \in P} \frac{1}{p}\right)\left(\sum_{q \in Q} \frac{1}{q}\right) = 1
$$

### Plain Language

Are there two finite sets of primes P, Q with (Σ 1/p)(Σ 1/q) = 1? The prime version is OPEN. The coprime version was solved by Cambie: (1 + 1/5)(1/2 + 1/3) = 1.

The Lean formalization has 2 sorries for supporting lemmas:
1. `prime_sets_disjoint`: If P,Q are sets of primes with reciprocal product = 1, then P∩Q=∅
2. `prime_set_size_lower_bound`: Such sets must have |P∪Q| ≥ 60

### Why This Matters

Concrete number theory problem about prime reciprocal sums with connections to Egyptian fraction theory. The supporting lemmas involve p-adic valuation arguments and Mertens-type estimates.

## Known Results

### What's Already Proven

- Coprime version solved: (1 + 1/5)(1/2 + 1/3) = 1 (Cambie)
- Main theorem stated with `axiom noSolutionForPrimeSets` (the open conjecture)
- Framework for prime sets, reciprocal products, and basic inequalities in place

### Our Goal

Prove the two supporting lemmas:
1. **Disjointness**: p-adic valuation argument — if p ∈ P∩Q, then v_p((Σ 1/p)(Σ 1/q)) < 0, contradiction
2. **Size lower bound**: Mertens-type lower bound showing any such configuration needs ≥ 60 primes

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `erdos-307` | Direct parent — inspect `Erdos307Problem.lean` for sorry locations (lines 172, 229) |

## Initial Thoughts

### Potential Approaches

1. **p-adic valuation for disjointness**: If p ∈ P∩Q, the p-adic valuation of (Σ 1/p)(Σ 1/q) is negative (from p's contribution), contradicting the product being an integer ≤ 1.
   - Mathlib has `padicValRat`, `Finset.sum` valuation lemmas
   - Risk: p-adic valuation over `Finset` sums may need custom bounds

2. **Mertens' theorem for size bound**: Mertens: Σ_{p≤n} 1/p ≈ log log n. For the product to reach 1, each sum must be at least ~1/sqrt(n). This forces many primes.
   - Mathlib has `Nat.Primorial`, partial Mertens results
   - Risk: Full Mertens may not be in Mathlib; may need weaker bound

### Key Difficulties

- p-adic valuation over finite prime sums in Lean
- Mertens-type estimates may not be in Mathlib in the exact form needed

### What Would a Proof Need?

- `padicValRat.sum_primes` or related p-adic lemmas
- `Nat.Mertens` or weaker prime reciprocal sum lower bounds
- `Finset.prod` and `Finset.sum` arithmetic

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Both sorries have clear mathematical strategies
- p-adic valuation approach is standard but Lean mechanization is non-trivial
- Mertens bound may require creative use of available Mathlib tools
- 60-prime lower bound is a specific concrete target

## References

### Papers
- Cambie, S. — Coprime solution to the prime reciprocal product problem

### Mathlib
- `Mathlib.NumberTheory.Padics.PadicVal` — p-adic valuations
- `Mathlib.NumberTheory.PrimeCounting` — prime counting and estimates

## Metadata

```yaml
tags:
  - erdos
  - number-theory
  - primes
  - egyptian-fractions
  - reciprocals
  - p-adic
related_proofs:
  - erdos-307
difficulty: medium
source: gallery-gap
created: 2026-04-03
```

**Significance**: 7/10
**Tractability**: 6/10
