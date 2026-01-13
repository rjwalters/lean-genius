# Erdős Problem #69: Irrationality of ∑ω(n)/2^n

## Problem Statement

Is ∑_{n≥2} ω(n)/2^n irrational?

Where ω(n) counts the number of distinct prime divisors of n.

## Status

**PROVED** by Tao-Teräväinen (2025)

## Key Insight (Tao's Observation)

The identity:
```
∑_{n≥2} ω(n)/2^n = ∑_{p prime} 1/(2^p - 1)
```

This reduces Problem 69 to a special case of Problem 257.

### Proof Sketch

1. ω(n) = ∑_{p|n} 1 (sum over prime divisors)
2. Swap order of summation: ∑_n (∑_{p|n} 1)/2^n = ∑_p ∑_{n: p|n} 1/2^n
3. For each prime p, sum over multiples: ∑_{k≥1} 1/2^(pk) = 1/(2^p - 1) (geometric)
4. Result: ∑_p 1/(2^p - 1)

## Session History

### Session 2026-01-13

**Mode**: REVISIT (pool empty)
**Outcome**: Progress - added infrastructure lemmas

#### What I Did

1. Reviewed existing Erdős 69 proof file
2. Added helper lemmas:
   - `two_pow_gt_one`: For p ≥ 2, 2^p > 1
   - `geometric_sum_over_multiples`: ∑_{k≥1} 1/2^(pk) = 1/(2^p - 1)
   - `omega_eq_card_prime_divisors`: ω(n) = |primeFactors(n)|
   - `summable_one_div_two_pow`: ∑ 1/2^n converges
3. Identified 4 sorries:
   - `summable_omega_div_pow` (HARD)
   - `summable_prime_sum` (HARD)
   - `tao_identity` (HARD - double sum manipulation)
   - `primeSum_irrational` (OPEN - requires Tao-Teräväinen deep result)

#### Key Findings

- **Mathlib has `Summable.tsum_comm`** for swapping double sums (in `Mathlib.Topology.Algebra.InfiniteSum.Constructions`)
- For ENNReal (non-negative extended reals), `ENNReal.tsum_comm` works unconditionally
- For general sums, need to prove absolute summability first
- The tao_identity proof requires:
  1. Expressing ω(n) as finite sum over primeFactors
  2. Using `Summable.tsum_comm` with appropriate summability hypotheses
  3. Recognizing geometric series in the inner sum

#### Aristotle Job Status

- **Project ID**: 07447536-f94a-409e-87eb-de15f0868c09
- **Submitted**: 2026-01-13T16:19:19Z
- **File**: proofs/Proofs/Erdos69Problem.lean
- **Status**: Submitted (waiting)
- **Targets**: `tao_identity`, `primeSum_irrational`

#### Next Steps

1. Wait for Aristotle results on tao_identity
2. If Aristotle fails, manually implement:
   - Prove ω bound: ω(n) ≤ log₂(n) for n ≥ 2
   - Use comparison test for summability
   - Prove double sum interchange with Summable.tsum_comm
3. For primeSum_irrational: This is essentially the Tao-Teräväinen 2025 result
   - May need to axiomatize if proof is too deep
   - Or find elementary alternative

#### Classification

| Sorry | Classification | Notes |
|-------|---------------|-------|
| summable_omega_div_pow | HARD | Comparison with ∑n/2^n |
| summable_prime_sum | HARD | Comparison with ∑1/2^p |
| tao_identity | HARD | Double sum manipulation |
| primeSum_irrational | OPEN | Tao-Teräväinen 2025 |

## References

- [Tao-Teräväinen 2025] - Irrationality of sums of reciprocals of exponentials minus 1
- Problem 257 on erdosproblems.com (more general statement)
- Mathlib: `Summable.tsum_comm` in InfiniteSum.Constructions
