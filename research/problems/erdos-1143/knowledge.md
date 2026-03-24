# Erdős #1143 - Knowledge Base

## Problem Statement

Estimate F_k(p₁,...,pᵤ), the minimum number of integers in any interval of k
consecutive integers divisible by at least one of the primes p₁,...,pᵤ.

## Status

**Erdős Database Status**: OPEN
**Phase**: ACT (actively proved theorems)
**Sorries**: 0 (all proved)
**Axioms**: 3 (deep results)

## Key Results

- `single_prime_lower`: Proved. In any k consecutive integers, ≥ k/p are divisible by p.
  - Technique: injection via ceiling division. Map i ↦ p*(⌈a/p⌉+i) from range(k/p).
  - Strengthened: works for all k, not just k ≥ 1.
- `single_prime_upper`: Already proved. At most k/p + 1 are divisible by p.
- `covering_le_k`: Already proved. Trivially F_k ≤ k.
- `expectedDensity_pos`, `expectedDensity_lt_one`: Already proved.
- `density_two_three`, `density_two_three_five`: Already proved.

## Sessions

### Session 2026-03-24 (Session 1) - Prove single_prime_lower

**Mode**: REVISIT (in-progress problem, knowledge score 9)
**Outcome**: completed (sorry eliminated)

#### What I Did
- Proved `single_prime_lower` by constructing an explicit injection
- Key insight: use b = (a + p - 1) / p as ceiling division to find first multiple of p ≥ a
- Map i ↦ p*(b+i) sends Finset.range(k/p) injectively into multiples of p in [a, a+k)
- Used Finset.card_image_of_injOn + Finset.card_le_card for the cardinality argument

#### Technical Notes
- omega cannot see definitional equalities from `set` - need explicit type ascriptions
- Nat.div_add_mod returns `p * ((a+p-1)/p) + mod = a+p-1` but omega needs `p * b + mod` explicitly
- Nat.div_mul_le_self has multiplication in `(n/k)*k` order, need mul_comm for `k*(n/k)`
- Finset.card_le_card_of_injOn uses Set coercions; cleaner to use image + card_le_card instead
- Strengthened theorem: removed `hk : k ≥ 1` hypothesis (proof works for k = 0 too)

#### Files Modified
- proofs/Proofs/Erdos1143Problem.lean (line 69-119: full proof of single_prime_lower)
- src/data/proofs/erdos-1143/meta.json (sorries: 1→0, line count updated)
- src/data/research/problems/erdos-1143.json (knowledge updated)

#### Next Steps
- Replace covering_complement_relation placeholder (True) with actual Jacobsthal connection

---

*Generated from erdosproblems.com on 2026-01-15*
