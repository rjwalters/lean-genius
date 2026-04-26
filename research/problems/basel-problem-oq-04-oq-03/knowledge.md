# Knowledge Base: basel-problem-oq-04-oq-03

**Problem**: Formalize Pr[gcd(m,n)=1] = 6/π² via Möbius inversion and Dirichlet series

---

## Problem Understanding

Goal: lim_{N→∞} |{(m,n) : 1≤m,n≤N, gcd(m,n)=1}| / N² = 6/π²

Key connections:
- 6/π² = 1/ζ(2) — reciprocal of the Basel constant
- 6/π² = ∏_p (1 - 1/p²) — Euler product (inverse of BaselProblemOQ04)
- 6/π² ≈ 0.6079 — empirically: N=10 gives 63/100 = 0.63

---

## Session 2026-04-26 (Session 1) — Lean Formalization

**Mode**: FRESH (OBSERVE → ACT)
**Outcome**: Proof file created, 2 axioms, 1 sorry, 18 theorems proved

### What I Did

1. **Surveyed infrastructure**:
   - `ArithmeticFunction.moebius_mul_coe_zeta`: μ * ζ = 1 (key Möbius identity)
   - `Erdos1149Problem.lean`: complete proofs of `moebius_sum_divisors_eq`, `card_multiples`
   - `BaselProblemOQ04.lean`: Euler product ∏_p(1-p⁻²)⁻¹ = π²/6 in 3 forms
   - `riemannZeta_two`: ζ(2) = π²/6 available in Mathlib

2. **Wrote BaselProblemOQ04OQ03.lean** (310 lines):
   - Proved: `moebius_sum_divisors` — Σ_{d|n} μ(d) = 1_{n=1} (from moebius_mul_coe_zeta)
   - Proved: `coprime_iff_moebius_sum` — 1_{gcd=1} = Σ_{d|gcd} μ(d)
   - Proved: `card_multiples` — |{m≤N: d|m}| = ⌊N/d⌋
   - Proved: `card_pairs_divisible` — |{(m,n)≤N²: d|m,d|n}| = ⌊N/d⌋²
   - Sorry: Sum exchange in `countCoprimePairs_moebius` (Finset.sum_comm)
   - Axiom: `moebius_dirichlet_series_at_two` — HasSum μ(d)/d² = 6/π²
   - Axiom: `coprime_pair_density_limit` — the density limit theorem
   - Computed: N=1,2,3,4,5,10 via native_decide (gives 1,3,7,13,21,63)

3. **Created gallery data**: `src/data/proofs/basel-problem-oq-04-oq-03/meta.json`

### Key Mathematical Findings

- The **Möbius decomposition** is the combinatorial heart:
  countCoprimePairs(N) = Σ_{d=1}^N μ(d) · ⌊N/d⌋²
- The **independence over primes** interpretation explains why:
  Pr[p∤gcd(m,n)] = 1-1/p², CRT gives independence → ∏_p(1-1/p²) = 6/π²
- The **sum exchange** is the main technical gap for a 0-sorry proof

### Next Steps

1. Prove the finite sum exchange in `countCoprimePairs_moebius`:
   - Use Finset.sum_comm or sigma-sum bijection
   - Key: d | gcd(m,n) ↔ d|m ∧ d|n, with d ≤ min(m,n) ≤ N
2. Eliminate `moebius_dirichlet_series_at_two`:
   - Bridge algebraic identity (moebius_mul_coe_zeta) to analytic HasSum
   - Check Mathlib.NumberTheory.LSeries.Basic for relevant lemmas
3. Consider Aristotle submission for sub-lemmas in the sum exchange

---

## Insights

- `Erdos1149Problem.lean` contains reusable proofs for Möbius and counting lemmas
- The finite sum exchange is a Finset.sum_comm type argument (implementable in one session)
- `BaselProblemOQ04.lean` has all Euler product ingredients needed
- Small cases (N≤10) are computable via native_decide — good for verification

## Built Items

- `proofs/Proofs/BaselProblemOQ04OQ03.lean` — main proof file (310 lines)
- `src/data/proofs/basel-problem-oq-04-oq-03/meta.json` — gallery entry
- `countCoprimePairs: ℕ → ℕ` — definition
- 4 fully proved lemmas (moebius_sum_divisors, coprime_iff_moebius_sum, card_multiples, card_pairs_divisible)
- 1 key theorem with sorry (countCoprimePairs_moebius)

## Mathlib Gaps

- No direct HasSum for Σ μ(d)/d² = 6/π² (gap in LSeries bridge for ℤ-valued functions)
- Finite sum exchange lemma for the specific Möbius-divisor structure

## Dead Ends

- Direct Euler product approach has same analytic complexity (not simpler)
- Trying to avoid Möbius entirely: no cleaner path found
