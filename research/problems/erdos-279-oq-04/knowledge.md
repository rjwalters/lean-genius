# Erdős 279 OQ-04: Formalize Density Definitions via Mathlib Asymptotic Analysis

## Problem Summary

Formalize the density conditions from Erdős Problem 279's generalization. The parent
proof (Erdos279Problem.lean) uses placeholder `True` bodies for:
- `HasPrimeLikeDensity A`: should be `∃ c > 0, ∀ᶠ N, c·N/log N ≤ |A ∩ [1,N]|`
- `HasLogLogDivergence A`: should be `∑_{n∈A,n≤N} 1/n − log(log N) → +∞`

The goal is to provide rigorous Mathlib-based formal definitions and basic properties.

## Session 2026-04-05 (Session 1) — Formal Definitions Proved

**Mode**: FRESH
**Outcome**: progress

### What I Did

- Created `proofs/Proofs/Erdos279OQ04.lean` with formal Mathlib definitions
- Replaced both `True` placeholders with genuine asymptotic definitions
- Used `Filter.atTop` and `Filter.Eventually` for the density condition
- Used `Set.indicator` in `reciprocalPartialSum` to avoid `DecidablePred`
- Proved 5 theorems fully (monotonicity ×4, infinitude ×1)
- Added 2 axioms (primes satisfy both conditions — PNT/Mertens not in Mathlib)
- 1 sorry: `tendsto_atTop_mul_div_log` (c·N/log N → ∞, HARD for Aristotle)
- Build verified: `=== Build succeeded ===`

### Key Findings

- `Set.indicator` cleanly handles membership without decidability requirements
- `Set.ncard_le_ncard` + `Set.Finite.subset` handle monotonicity of counting function
- `tendsto_atTop_mono` from Mathlib handles log-log divergence monotonicity in one line
- The infinitude proof via contradiction works cleanly: finite A → bounded count → contradiction with c·N/log N → ∞
- Both PNT lower bound and Mertens' theorem are absent from Mathlib, requiring axioms

### Files Modified

- `proofs/Proofs/Erdos279OQ04.lean` (new, 103 lines)
- `proofs/Proofs.lean` (added import)

### Next Steps

1. Submit `tendsto_atTop_mul_div_log` sorry to Aristotle
   - Key lemma: `Real.isLittleO_log_id_atTop` gives `log x = o(x)`
   - From this, `x/log x → ∞` follows
2. Consider proving PNT lower bound from existing Chebyshev bound in `Erdos31PrimesDensity.lean`
   - That file proves π(N) ≤ 2N·log(4)/log(N) + √N + 1 (upper bound)
   - Lower bound needs Bertrand's postulate or separate argument
3. Consider formalizing Mertens' second theorem for complete proof
