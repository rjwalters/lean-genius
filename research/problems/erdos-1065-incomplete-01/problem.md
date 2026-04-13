# Erdős Problem #1065: Primes of the Form 2^k · q + 1

**Lean file**: `proofs/Proofs/Erdos1065BatemanHorn.lean`
**Sorries**: 1
**Status**: available
**Tier**: B | **Significance**: 7/10 | **Tractability**: 7/10

## Problem Statement

Erdős #1065: Are there infinitely many primes of the form $2^k \cdot q + 1$ where $q$ is an odd prime and $k \geq 1$? (Bateman-Horn conjecture application)

## The Sorry

```lean
-- In a theorem about unique factorization of 2^k * q:
sorry -- Requires 2-adic valuation argument: v₂(2^k·q) = k when q is odd,
      -- so k₁ = k₂ from heq, then q₁ = q₂ by cancellation.
      -- Aristotle candidate for companion file.
```

**Why tractable**: This is a concrete p-adic valuation fact. Mathlib has `Nat.factorization` and `Nat.ord_compl` tools. The key lemma is: if `2^k₁ * q₁ = 2^k₂ * q₂` where q₁, q₂ are odd, then k₁ = k₂ and q₁ = q₂.

## Approach

1. Use `Nat.factorization_mul` and `Nat.factorization_pow`
2. The 2-adic valuation of `2^k * q` where q is odd: `(2^k * q).factorization 2 = k`
3. This gives k₁ = k₂, then q₁ = q₂ by cancellation
4. Key lemmas: `Nat.Coprime.pow_dvd_of_pow_dvd`, `Nat.odd_iff`, `Nat.factorization`

## Key Mathlib APIs

- `Nat.factorization_mul (hn : n ≠ 0) (hm : m ≠ 0)`
- `Nat.factorization_pow`
- `Nat.Odd.factorization_two_eq_zero : Odd n → n.factorization 2 = 0`
- `padicValNat 2 (2^k * q)` if q is odd = k

## Related Gallery Proof

- `src/data/proofs/erdos-1065/` — Erdős Problem #1065 base proof
- `proofs/Proofs/Erdos1065BatemanHorn.lean` — file with sorry

## First Steps (OBSERVE phase)

1. Read `Erdos1065BatemanHorn.lean` completely
2. Find the exact theorem containing the sorry
3. Try: `Nat.factorization_mul_of_pos` + `Nat.Odd.factorization_two_eq_zero`
4. Check if `omega` or `simp` with factorization lemmas closes the goal
