# Erdős Problem #1099: Divisor Ratio Sum Boundedness

**Problem**: For α > 1, is liminf h_α(n) bounded, where h_α(n) = Σ((d_{i+1}/dᵢ) - 1)^α?
**Answer**: YES (Vose, 1984)
**Status**: IN-PROGRESS (0 sorries, 4 axioms)

## Current State

- **File**: `proofs/Proofs/Erdos1099Problem.lean` (542 lines, 24 theorems)
- **Sorries**: 0
- **Axioms**: 4 (vose_bounded_sequence, vose_liminf_bounded, sum_divisor_ratios_lower_bound, power_of_two_h_alpha)
- All theorems are sorry-free

## Session 2026-03-25 (Session 2) - Prove h_alpha_ge_one and prime_h_alpha_unbounded

**Mode**: REVISIT (MODERATE knowledge, score 12)
**Outcome**: progress (5A+1S → 4A+0S)

### What I Did
- Proved `zipWith_div_ge_one`: consecutive ratios in sorted positive lists are ≥ 1 (by list induction)
- Proved `divisorRatios_ge_one`: all divisor ratios are ≥ 1 (corollary)
- Completed `h_alpha_ge_one` proof: used nonneg terms + `List.single_le_sum` to show sum ≥ largest term ≥ 1
- Proved `prime_ratio_mem`: for prime p, the ratio p/1 = p appears in divisorRatios (via `Nat.Prime.eq_one_or_self_of_dvd`)
- Converted `prime_h_alpha_unbounded` from axiom to theorem: for any M, find prime p with p-1 > M, then h_α(p) ≥ (p-1)^α ≥ p-1 > M

### Key Findings
- `le_div_iff` + `Nat.cast_le` handles the ratio ≥ 1 proof cleanly
- `Real.rpow_nonneg` requires `0 ≤ base`; for ratios ≥ 1, `base = ratio - 1 ≥ 0` works
- `Real.rpow_le_rpow_left` gives exponent monotonicity: x^1 ≤ x^α when x ≥ 1, α ≥ 1
- `Nat.exists_infinite_primes` + natural ceiling gives prime p > M+1

### Files Modified
- `proofs/Proofs/Erdos1099Problem.lean` (458→542 lines, +5 theorems, -1 axiom, -1 sorry)
- `src/data/proofs/erdos-1099/meta.json` (updated counts)
- `src/data/research/problems/erdos-1099-oq-01.json` (updated knowledge)

### Next Steps
- Prove `power_of_two_h_alpha` via `Nat.divisors_prime_pow` + sorted list of powers of 2
- Prove `sum_divisor_ratios_lower_bound` via AM-GM + telescoping product (Πrᵢ = n)
