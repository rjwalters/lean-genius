# Erdős Problem #433: Maximum Frobenius Numbers

**Lean file**: `proofs/Proofs/Erdos433Problem.lean`
**Sorries**: 1
**Status**: available
**Tier**: B | **Significance**: 7/10 | **Tractability**: 7/10

## Problem Statement

Erdős #433: Let $g(k, n)$ be the maximum Frobenius number over all $k$-element sets of integers up to $n$ with gcd 1. What is the growth rate of $g(k, n)$?

## The Sorry

```lean
theorem g_two (n : ℕ) (hn : n ≥ 3) : g 2 n = n^2 - 3*n + 1 := by
  sorry -- Follows from Sylvester-Frobenius applied to {n-1, n}
```

**Why tractable**: The Chicken McNugget / Sylvester-Frobenius theorem gives: for two coprime positive integers $a, b$, the Frobenius number is $ab - a - b$. With $a = n-1, b = n$: Frobenius = $(n-1)n - (n-1) - n = n^2 - n - n + 1 - n = n^2 - 3n + 1$.

## Key Mathematical Content

- Sylvester-Frobenius: `Frobenius(a, b) = a*b - a - b` when `gcd(a,b) = 1`
- `gcd(n-1, n) = 1` always (consecutive integers are coprime)
- This set maximizes the Frobenius number among 2-element subsets of {1,...,n}

## Approach

1. Show `gcd(n-1, n) = 1`: `Nat.Coprime.symm (Nat.coprime_succ_self (n-1))`
2. Apply `Nat.subtype.numeralSubtype` or direct calculation
3. Frobenius number formula: if Mathlib has it, use directly; otherwise prove it
4. Show {n-1, n} achieves the maximum among all 2-element subsets

## Key Mathlib APIs

- `Nat.Coprime` and related lemmas
- `Nat.coprime_succ_self`
- Check if `Mathlib.RingTheory.Frobenius` or `Mathlib.NumberTheory.LucasPrimality` has Frobenius number
- `Finset.sup` for maximization

## Related Gallery Proof

- `src/data/proofs/erdos-433/` — Erdős Problem #433
- `proofs/Proofs/Erdos433Problem.lean` — file with sorry

## First Steps (OBSERVE phase)

1. Read `Erdos433Problem.lean` to understand the definition of `g`
2. Search Mathlib for Frobenius number: `#check Nat.card_add_card_le`
3. Verify the formula numerically for small n (n=3: 9-9+1=1; {2,3} → Frobenius=1 ✓)
4. Check if `omega` can close the main formula goal after establishing coprimality
