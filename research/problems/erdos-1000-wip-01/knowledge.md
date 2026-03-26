# Research Knowledge: erdos-1000-wip-01

## Problem
Complete Erdős #1000: Generalized Totients and Diophantine Approximation.
The existing formalization has 4 axioms (erdos_no_zero_limit, erdos_dichotomy, cassels_liminf_zero, haight_resolution) and 0 sorries. Goal: prove one or more axioms.

## Summary
Session 1 proved structural lower bounds. Session 2 proved the complement formula and 6 more infrastructure theorems, establishing the framework for proving erdos_no_zero_limit via a double-counting argument.

## Session 2026-03-25 (Session 1) - Structural Lower Bound

**Mode**: FRESH
**Outcome**: progress

### What I Did
- Proved `phiA_ge_totient`: φ_A(k) ≥ φ(n_k) for any increasing sequence A
  - Key insight: coprime elements always pass the phiA filter
  - If gcd(m, n_k) = 1, then reducedDenom m n_k = n_k > n_j for all j < k
  - Proof: subset argument — (range n).filter(Coprime n) ⊆ (Icc 1 n).filter(phiA_cond)
- Proved `densityRatio_ge_totient_ratio`: ρ_A(k) ≥ φ(n_k)/n_k
- Fixed Mathlib API migration issues (∑ in → ∈, omega, division lemmas)

### Key Findings
- Lower bound φ_A(k) ≥ φ(n_k) is NOT sufficient for erdos_no_zero_limit
  - φ(n_k)/n_k CAN go to 0 (e.g., primorial sequence)
  - Need deeper structural argument

## Session 2026-03-26 (Session 2) - Complement Formula

**Mode**: REVISIT
**Outcome**: progress

### What I Did
- Proved `phiA_add_used`: φ_A(k) + Σ_{used e|n_k} φ(e) = n_k (complement formula)
  - Uses Finset.sum_filter_add_sum_filter_not + Nat.sum_totient
- Proved `used_sum_le`: used φ-sum ≤ n_k - φ(n_k)
  - n_k is always unused; from phiA_add_used + phiA_ge_totient
- Proved `used_card_le`: at most k divisors are used
  - Each used divisor maps injectively to j < k via A.seq
- Proved `phiA_pos`: φ_A(k) ≥ 1
- Proved `densityRatio_pos`: ρ_A(k) > 0
- Proved `densityRatio_complement`: ρ_A(k) = 1 - used/n_k in ℝ
- Proved `densityRatio_ge_of_prime`: ρ_A(k) ≥ 1/2 when n_k is prime

### Key Findings
- Complement formula reframes erdos_no_zero_limit: for ρ → 0, used divisors must capture almost ALL of n_k's φ-sum. At most k divisors can do this, and n_k is always excluded.
- **erdos_no_zero_limit proof approach**: Double-count Σ_k (1-ρ_A(k)). Switch sum order: Σ_j φ(n_j) · Σ_{k>j: n_j|n_k} 1/n_k. Inner sum = reciprocals of multiples of n_j in the sequence. Bound by harmonic sum → contradiction.
- Blocked on: formalizing the double-counting + real-valued sum bounds

### Files Modified
- `proofs/Proofs/Erdos1000Problem.lean` — 7 new theorems (370→607 lines)
- `src/data/proofs/erdos-1000/meta.json` — updated
- `src/data/research/problems/erdos-1000-wip-01.json` — updated

### Next Steps
- Formalize the double-counting argument for erdos_no_zero_limit
- Alternative: prove for special cases first (lacunary, prime-rich sequences)
- cassels_liminf_zero requires continued fraction construction (longer-term)
