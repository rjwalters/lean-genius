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

### Session 2026-01-13 (Session 2) - Summability Complete

**Mode**: REVISIT (continuation)
**Outcome**: Major progress - 4 sorries → 1 sorry

#### What I Did

1. **Proved `omega_le_self`**: ω(n) ≤ n for all n
   - Case n=0,1: trivial (ω=0)
   - Case n≥2: primeFactors(n) ⊆ Finset.Icc 2 n, card ≤ n-1 < n
   - Uses `Nat.card_Icc`, `Nat.le_of_mem_primeFactors`

2. **Proved `summable_omega_div_pow`**: ∑ω(n)/2^n converges
   - Comparison with ∑n/2^n using `omega_le_self`
   - Uses `Summable.of_norm_bounded`, `summable_pow_mul_geometric_of_norm_lt_one`

3. **Proved `summable_prime_sum`**: ∑_p 1/(2^p-1) converges
   - Comparison: 1/(2^p-1) ≤ 2/2^p (proved as `one_div_two_pow_sub_one_le`)
   - Uses subseries of geometric: `summable_one_div_two_pow.subtype _`

4. **Axiomatized `primeSum_irrational`**:
   - Converted to axiom citing Tao-Teräväinen 2025
   - Deep analytic number theory beyond current Mathlib

5. **Documented `tao_identity`**:
   - Added detailed proof requirements
   - Needs Fubini-type exchange (Summable.tsum_comm)
   - Infrastructure exists but bijection setup is complex

#### Current State

| Component | Status |
|-----------|--------|
| `omega_le_self` | PROVED |
| `summable_one_div_two_pow` | PROVED |
| `summable_omega_div_pow` | PROVED |
| `summable_prime_sum` | PROVED |
| `one_div_two_pow_sub_one_le` | PROVED |
| `geometric_sum_over_multiples` | PROVED |
| `tao_identity` | 1 SORRY (HARD) |
| `primeSum_irrational` | AXIOM (Tao-Teräväinen 2025) |

#### Next Steps

1. Attempt `tao_identity` using `Summable.tsum_comm`
2. Key challenge: expressing (n, p|n) ↔ (p, k≥1) bijection in Lean
3. Alternative: submit to Aristotle for overnight processing

---

### Session 2026-01-13 (Session 1)

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

#### Classification (Original - Now Updated)

| Sorry | Classification | Status |
|-------|---------------|--------|
| summable_omega_div_pow | HARD | **PROVED** (Session 2) |
| summable_prime_sum | HARD | **PROVED** (Session 2) |
| tao_identity | HARD | REMAINING (1 sorry) |
| primeSum_irrational | OPEN | **AXIOM** (cited result) |

## References

- [Tao-Teräväinen 2025] - Irrationality of sums of reciprocals of exponentials minus 1
- Problem 257 on erdosproblems.com (more general statement)
- Mathlib: `Summable.tsum_comm` in InfiniteSum.Constructions
