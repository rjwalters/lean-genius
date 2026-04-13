# Problem: Prove formA_decomposition_unique from Nat.multiplicity

**Slug**: erdos-1065-oq-05-oq-01
**Created**: 2026-04-05T05:56:11-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The key claim is that for any natural number $n = 2^k \cdot q$ where $q$ is odd, the 2-adic valuation satisfies:

$$
\nu_2(2^k \cdot q) = k
$$

In Lean 4: `Nat.multiplicity 2 (2^k * q) = k` when `q` is odd.

The broader goal is to prove `formA_decomposition_unique` in the Bateman-Horn proof context: if `p - 1 = 2^k * q` with `q` odd, this decomposition is unique (i.e., `k` is the exact 2-adic valuation of `p - 1`).

### Plain Language

Given an odd number $q$ and a natural number $k$, we want to prove that $2^k \cdot q$ has exactly $k$ factors of 2 — no more, no fewer. This uniquely determines the "Form A" decomposition of any even number as a power of 2 times an odd number.

### Why This Matters

The `erdos-1065-oq-05` gallery proof uses `formA_decomposition_unique` as an axiom. Proving it from Mathlib's `Nat.multiplicity` would remove that axiom, and could contribute a useful lemma to Mathlib.

## Known Results

### What's Already Proven

- Mathlib has `Nat.multiplicity_pow_self` — handles `multiplicity p (p^n) = n`
- Mathlib has `multiplicity.mul` — handles additivity `multiplicity p (a * b)`
- The 2-adic valuation of odd numbers is 0 (follows from coprimality)

### Our Goal

Prove `formA_decomposition_unique` as a theorem (not axiom) using Mathlib's `Nat.multiplicity` or `padicValNat` API.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| erdos-1065 | Primes of form 2^k·q+1 (grandparent) |
| erdos-1065-oq-05 | Bateman-Horn Density (direct parent, contains axiom) |

## Initial Thoughts

### Potential Approaches

1. **Direct multiplicity calculation**:
   - Use `Nat.multiplicity_pow_self` for the `2^k` part
   - Use odd number coprimality for `multiplicity 2 q = 0`
   - Combine via `multiplicity.mul` (additivity)

2. **Via padicValNat** (possibly cleaner):
   - `padicValNat 2 (2^k * q) = k` when `q` is odd
   - Mathlib has `padicValNat.prime_pow_self` and `padicValNat.mul`

3. **Case split on k = 0**:
   - `k = 0`: reduces to `multiplicity 2 q = 0` (q odd)
   - `k > 0`: use induction or direct lemmas

### Key Mathlib Lemmas to Check

- `Nat.multiplicity_pow_self` / `emultiplicity_pow_self`
- `multiplicity.Finsupp.emultiplicity_pow_self`
- `padicValNat.prime_pow_self`, `padicValNat.mul`
- `Nat.Odd.not_two_dvd_nat` or `Nat.Coprime.multiplicity_eq_zero`

## Tractability Assessment

**Difficulty**: Low

**Justification**: Concrete arithmetic fact with all ingredients in Mathlib. The `padicValNat` API may give the most direct path. Similar 2-adic valuation computations appear throughout Mathlib.

**Estimated Effort**: 1-2 days (mostly finding exact API names)

## Metadata

```yaml
tags:
  - arithmetic
  - lean-mathlib
  - 2-adic-valuation
  - multiplicity
  - erdos
related_proofs:
  - erdos-1065
  - erdos-1065-oq-05
difficulty: low
source: gallery-gap
created: 2026-04-05T05:56:11-07:00
```
