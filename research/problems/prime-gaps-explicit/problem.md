# Problem: Explicit Prime Gap Bounds

**Slug**: prime-gaps-explicit
**Created**: 2025-12-31
**Status**: Active
**Source**: feasibility-analysis

## Problem Statement

### Formal Statement

$$
p_n \leq 2^n \quad \text{for all } n \geq 1
$$

### Plain Language

The n-th prime is bounded above by 2^n. This follows from Bertrand's postulate by induction: if there's always a prime between n and 2n, then primes can't grow faster than doubling.

### Why This Matters

1. **Explicit bounds**: Concrete numerical inequality, not asymptotic
2. **Bertrand application**: Shows how to derive consequences from postulate
3. **Prime distribution**: Quantitative control on prime spacing

## Known Results

### What's Already Proven

- **primeCounting (π)** — In Mathlib
- **Bertrand's postulate** — Prime in (n, 2n), in Mathlib
- **add_two_le_nth_prime** — p_n ≥ n + 2

### What's Still Open (for us)

- Prove p_n ≤ 2^n from Bertrand
- Prove π(2n) > π(n)

### Our Goal

```lean
theorem nth_prime_le_two_pow (n : ℕ) (hn : n ≥ 1) :
    Nat.nth Prime n ≤ 2^n
```

## Tractability Assessment

**Significance**: 4/10
**Tractability**: 8/10

**Justification**:
- Direct induction from Bertrand's postulate
- Uses existing Mathlib infrastructure
- Weak but explicit bound

## Metadata

```yaml
tags:
  - number-theory
  - primes
  - explicit-bounds
  - bertrand
difficulty: medium
source: feasibility-analysis
created: 2025-12-31
```
