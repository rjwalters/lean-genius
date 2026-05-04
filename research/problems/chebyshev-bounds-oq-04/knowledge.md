# chebyshev-bounds-oq-04: Second Chebyshev Function ψ(n) Bounds

## Problem Summary

Formalize the second Chebyshev function ψ(n) = Σ_{k≤n} Λ(k) and prove:
1. θ(n) ≤ ψ(n) (first ≤ second Chebyshev function)
2. ψ(2n) - ψ(n) ≥ log(n+1) for n ≥ 1 (Bertrand lower bound)
3. ψ(n) ≤ 2n·log 2 (Chebyshev upper bound)
4. ψ(n)/n → 1 (Prime Number Theorem for ψ)

## Status

**PROGRESS** — PR #15371 merged (initial file, θ≤ψ and Bertrand lower bound proved, upper bound + PNT axiomatized). PR #15413 in progress: converting `chebyshevPsi_doubling_le` from axiom to theorem.

## Session 2026-05-03 (Session 1) - Initial formalization

**Mode**: FRESH  
**Outcome**: completed (PR #15371 merged)

### What I Did
- Created ChebyshevBoundsOQ04.lean with:
  - chebyshevPsi definition
  - θ≤ψ proof via vonMangoldt subset sum
  - Bertrand lower bound: ψ(2n)-ψ(n) ≥ log(n+1)
  - chebyshevPsi_doubling_le axiomatized (4 axioms total)

### Files Modified
- proofs/Proofs/ChebyshevBoundsOQ04.lean (new)
- src/data/proofs/chebyshev-bounds-oq-04/ (new gallery entry)

---

## Session 2026-05-04 (Session 2) - Axiom reduction + Mathlib drift fix

**Mode**: REVISIT  
**Outcome**: progress (PR #15413 open)

### What I Did
- Replaced `axiom chebyshevPsi_doubling_le` with theorem structure:
  - `private theorem psi_doubling_le_log_centralBinom` (1 sorry): encodes vonMangoldt/Fubini identity log(C(2n,n)) ≥ ψ(2n)-ψ(n)
  - `theorem chebyshevPsi_doubling_le`: fully proved outer bound via Nat.centralBinom_le_four_pow + Real.log_pow
- Fixed Mathlib API drift: `Nat.exists_prime_lt_and_le_two_mul_add_one` → `Nat.bertrand`
- Fixed `chebyshevPsi_bounds` n=1 edge case (n/2=0 case) using rcases + psi monotonicity
- Created ChebyshevBoundsOQ04Aristotle.lean companion for Aristotle
- Submitted Aristotle job: `a6b2d46e-90cf-4f96-a532-c704bee322da`

### Key Findings
- `Nat.bertrand (n : ℕ) (hn : n ≠ 0) : ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n` — current API takes `n ≠ 0`, use `by omega` from `1 ≤ n`
- `Nat.centralBinom_le_four_pow` does NOT exist in Mathlib; must prove `C(2n,n) ≤ 4^n` inline via `Finset.single_le_sum + Nat.sum_range_choose`
- `vonMangoldt_nonneg` has `{k : ℕ}` fully implicit; `fun k _ => vonMangoldt_nonneg` in lambda doesn't work — must extract `have hf : ∀ k ∈ s, 0 ≤ vonMangoldt k := fun k _ => vonMangoldt_nonneg` with explicit type annotation
- `Finset.single_le_sum (hf) hmem` — element is ⦃⦄ semi-implicit; no extra `_` placeholder
- `Finset.sum_sdiff_eq_sub` cannot be used as `simp only` lemma with proof arg; use `Finset.sum_sdiff` in linarith instead
- `Real.log (n / 2 + 1)` with `n : ℕ` coerces to REAL division; use `(n / 2 : ℕ) + 1 : ℝ` for nat floor division
- `Finset.range_mono (by omega) : range (n+1) ⊆ range (2n+1)` — API confirmed working
- Naive induction from doubling lemma DOES NOT prove full ψ(n) ≤ 2n·log 2 (tested)
- vonMangoldt_sum identity: `Σ_{d ∈ n.divisors} Λ d = Real.log n`
- log(C(2n,n)) = Σ_d Λ(d)·(⌊2n/d⌋-2⌊n/d⌋) ≥ ψ(2n)-ψ(n) is the classical Chebyshev argument

### Net Effect
- axiomCount: 4 → 3 (chebyshevPsi_doubling_le converted to theorem)
- sorryCount: 0 → 1 (psi_doubling_le_log_centralBinom)
- Docker build: ✅ SUCCEEDED (exit 0, 3073 jobs) — PR #15413

### Next Steps
- Await Aristotle result for `psi_doubling_le_log_centralBinom` (job `a6b2d46e-90cf-4f96-a532-c704bee322da`)
- If Aristotle proves it: eliminate sorry, axiomCount 3, sorryCount 0
- Future: try to prove `chebyshevPsi_upper_bound` from `chebyshevPsi_doubling_le` (requires non-trivial telescoping argument)
