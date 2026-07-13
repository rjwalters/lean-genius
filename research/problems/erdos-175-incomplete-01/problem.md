# Erdős Problem #175: Central Binomial Coefficient Not Squarefree

**Lean file**: `proofs/Proofs/Erdos175Problem.lean`
**Sorries**: 1
**Status**: available
**Tier**: B | **Significance**: 7/10 | **Tractability**: 5/10

## Problem Statement

Erdős #175: Is C(2n, n) squarefree for infinitely many n? (Answer: probably only finitely many — the squarefree values are rare.)

## The Sorry

```lean
/-- 4 | C(2n, n) iff n is not a power of 2 -/
theorem four_divides_iff (n : ℕ) (hn : n ≥ 2) :
    4 ∣ centralBinom n ↔ ¬∃ k : ℕ, n = 2 ^ k := by
  sorry
```

**Why this is the key lemma**: If 4 | C(2n,n) for all n ≥ 2 except powers of 2, then C(2n,n) is squarefree only for n = 2^k.

## Mathematical Content

This follows from Kummer's theorem: the p-adic valuation of C(m+n, m) equals the number of carries when adding m and n in base p.

For p = 2: `v₂(C(2n,n))` = number of carries adding n+n in binary = number of 1-bits in n (Hamming weight).

So `4 ∣ C(2n,n)` iff `v₂(C(2n,n)) ≥ 2` iff `n` has ≥ 2 ones in binary iff n is not a power of 2.

## Approach

1. Use `Nat.factorization` or `multiplicity`
2. Key: `v₂(C(2n,n)) = n.bits.count true` (bits = binary representation)
3. n is a power of 2 iff exactly one bit is set
4. Look for `Nat.centralBinom_factorization` or similar in Mathlib
5. May need to use Kummer's theorem if available, or prove directly

## Key Mathlib APIs

- `Nat.centralBinom` (or define as `Nat.choose (2*n) n`)
- `multiplicity 2 (Nat.choose (2*n) n)`
- `Nat.Prime.multiplicity_choose_prime_pow`
- `Nat.bits` and `List.count`
- Kummer's theorem: search `Nat.multiplicity_choose`

## Related Gallery Proof

- `src/data/proofs/erdos-175/` — Erdős Problem #175
- `proofs/Proofs/Erdos175Problem.lean` — file with sorry

## First Steps (OBSERVE phase)

1. Read `Erdos175Problem.lean` fully
2. Check if `Nat.multiplicity_choose` or similar exists in Mathlib
3. Look at the definition of `centralBinom` used in this file
4. Check: is this Kummer's theorem or a simpler direct argument?
5. Try small cases: n=2 (C(4,2)=6=2·3, not divisible by 4); n=3 (C(6,3)=20=4·5, yes 4|20)
