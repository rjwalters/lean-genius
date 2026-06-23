# Feasibility Check: Legendre Conjecture Partial

**Date**: 2025-12-31
**Time spent**: ~10 minutes

## The Problem

**Legendre's Conjecture** (unsolved): For every positive integer n,
there exists a prime p with n² < p < (n+1)².

We aim to prove this for specific small values of n.

## Step 1: Mathlib Search Results

| Component | In Mathlib? | Notes |
|-----------|-------------|-------|
| Legendre's Conjecture | **NO** | Not formalized |
| Bertrand's Postulate | **YES** | Prime in (n, 2n] |
| Prime counting π(x) | **YES** | Full support |
| Decidable primality | **YES** | For computation |
| `Nat.Prime` | **YES** | Basic infrastructure |

## Step 2: Analysis

### Why Bertrand Doesn't Directly Help

- Bertrand: ∃ prime p with n < p ≤ 2n
- Legendre: ∃ prime p with n² < p < (n+1)²
- Gap for Legendre: 2n + 1
- Bertrand gives prime in (n², 2n²), but 2n² >> (n+1)² for large n

### What's Tractable

For small n, we can verify computationally:
- n = 1: (1, 4) contains 2, 3
- n = 2: (4, 9) contains 5, 7
- n = 3: (9, 16) contains 11, 13
- n = 4: (16, 25) contains 17, 19, 23
- n = 5: (25, 36) contains 29, 31
- ...

Each case can be verified by `native_decide`.

## Step 3: Milestone Tractability

| Milestone | Tractability | Notes |
|-----------|--------------|-------|
| Define Legendre statement | **10/10** | Simple definition |
| Verify n = 1 to 10 | **9/10** | native_decide |
| Verify n = 1 to 50 | **8/10** | native_decide |
| Verify n = 1 to 100 | **7/10** | May be slow |
| General conjecture | **0/10** | Unsolved |

## Step 4: Decision

**Assessment**: DEEP DIVE

**Rationale**:
1. Clear definition possible
2. Computational verification for many small n
3. Novel formalization
4. Educational value

## Implementation Plan

```lean
/-- Legendre's conjecture for a specific n -/
def LegendreAt (n : ℕ) : Prop :=
  ∃ p, Nat.Prime p ∧ n^2 < p ∧ p < (n+1)^2

/-- The full Legendre conjecture -/
def LegendreConjecture : Prop :=
  ∀ n ≥ 1, LegendreAt n

-- Verify specific cases
theorem legendre_one : LegendreAt 1 := by native_decide
theorem legendre_two : LegendreAt 2 := by native_decide
-- etc.
```

## Time Budget

~1 hour for definitions and ~20 verified cases
