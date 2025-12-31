# Feasibility Check: Explicit Prime Gap Bounds

**Date**: 2025-12-31
**Time spent**: ~15 minutes

## The Problem

**Dusart-type bounds**: Explicit inequalities for prime counting/gaps like:
- π(x) ≥ x/(ln x + 2) for x ≥ 55
- p_n ≤ n(ln n + ln ln n) for n ≥ 6
- There's a prime between n and n(1 + 1/(25 ln²n))

## Step 1: Mathlib Search Results

| Component | In Mathlib? | Notes |
|-----------|-------------|-------|
| `primeCounting` (π) | **YES** | Basic definition |
| `primeCounting'` (π') | **YES** | Off-by-one variant |
| `vonMangoldt` (Λ) | **YES** | For L-series |
| Bertrand's postulate | **YES** | Prime in (n, 2n) |
| Monotonicity of π | **YES** | Basic property |
| `add_two_le_nth_prime` | **YES** | p_n ≥ n + 2 |
| Dusart bounds | **NO** | Not formalized |
| Chebyshev bounds | **NO** | θ, ψ bounds missing |
| PNT-style explicit | **NO** | No asymptotic bounds |

## Step 2: Key Insight - What's Actually Provable

From Bertrand's postulate, we can derive:
- There exists a prime in (n, 2n) for n ≥ 1
- Therefore p_{k+1} ≤ 2 · p_k for all k
- By induction: **p_n ≤ 2^n**

This is a weak but explicit bound that's PROVABLE from what Mathlib has!

Additionally:
- From Bertrand: π(2n) > π(n) for n ≥ 1
- Small values can be computed: π(10) = 4, π(100) = 25

## Step 3: Milestone Tractability

| Milestone | Tractability | Notes |
|-----------|--------------|-------|
| Compute π(n) for small n | **10/10** | Decidable |
| Prove p_n ≤ 2^n | **8/10** | Induction from Bertrand |
| Prove π(2n) ≥ π(n) + 1 | **9/10** | Direct from Bertrand |
| Simple lower bound on π | **6/10** | Needs careful work |
| Dusart bound π(x) ≥ x/(ln x + 2) | **2/10** | Needs real analysis |
| Full Chebyshev bounds | **1/10** | Major undertaking |

## Step 4: Decision

**Assessment**: DEEP DIVE

**Rationale**:
- The bound p_n ≤ 2^n is non-trivial and follows from Bertrand
- Provides an explicit upper bound on the n-th prime
- Uses Mathlib's Bertrand proof as foundation
- Demonstrates technique for deriving explicit bounds

**Time budget**: 1-2 hours

## What We'll Prove

1. **`nth_prime_le_two_pow`**: p_n ≤ 2^n for all n ≥ 1
2. **`primeCounting_double_gt`**: π(2n) > π(n) for n ≥ 1
3. **Small computations**: π(10) = 4, π(20) = 8, etc.
4. **Consequence**: Explicit (weak) gap bound

## Technical Approach

```lean
-- Key lemma from Bertrand
theorem Nat.exists_prime_lt_and_le_two_mul (n : ℕ) (h : n ≥ 1) :
    ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n

-- Our target
theorem nth_prime_le_two_pow (n : ℕ) (hn : n ≥ 1) :
    Nat.nth Prime n ≤ 2^n
```

Proof by strong induction:
- Base: p_1 = 2 ≤ 2^1 ✓
- Step: By Bertrand, ∃ prime in (p_n, 2·p_n]
- So p_{n+1} ≤ 2·p_n ≤ 2·2^n = 2^{n+1} ✓
