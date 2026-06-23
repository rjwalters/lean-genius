# Erdős 279 OQ-04: Formalize Density Definitions via Mathlib Asymptotic Analysis

## Problem Summary

Formalize the density conditions from Erdős Problem 279's generalization. The parent
proof (Erdos279Problem.lean) uses placeholder `True` bodies for:
- `HasPrimeLikeDensity A`: should be `∃ c > 0, ∀ᶠ N, c·N/log N ≤ |A ∩ [1,N]|`
- `HasLogLogDivergence A`: should be `∑_{n∈A,n≤N} 1/n − log(log N) → +∞`

The goal is to provide rigorous Mathlib-based formal definitions and basic properties.

**Status: COMPLETED** — 0 sorries, 2 axioms. File: `proofs/Proofs/Erdos279OQ04.lean`

---

## Session 2026-04-05 (Session 1-2) — Formal Definitions Proved + Sorry Eliminated

**Mode**: FRESH
**Outcome**: completed

### What I Did

- Created `proofs/Proofs/Erdos279OQ04.lean` with formal Mathlib definitions
- Replaced both `True` placeholders with genuine asymptotic definitions
- Proved 5 theorems fully (monotonicity ×4, infinitude ×1)
- Proved `tendsto_atTop_mul_div_log` (c·N/log N → ∞) eliminating the last sorry
- Added 2 axioms (primes satisfy both conditions — PNT/Mertens not in Mathlib)
- Build verified: 0 sorries, 2 axioms, 127 lines

### Key Technical Insights

- `Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero` with `simp [pow_one, add_zero, one_mul]` gives `log x / x → 0`
- `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within` converts `nhds 0` to `nhds[>] 0` using `log x / x > 0` for `x > 1`
- `inv_tendsto_nhdsGT_zero` inverts `f → 0⁺` to get `f⁻¹ → ∞`
- `Filter.Eventually.of_forall` (NOT `Filter.eventually_of_forall`) for `h.congr'` steps
- `Tendsto.const_mul_atTop hc` multiplies by positive constant at the end
- `one_mul` must be in simp alongside `pow_one, add_zero` — `1 * x` doesn't simplify otherwise
- `Set.indicator` cleanly handles membership without decidability requirements
- `tendsto_atTop_mono` handles log-log divergence monotonicity in one line

### Files Created

- `proofs/Proofs/Erdos279OQ04.lean` (127 lines, 0 sorries, 2 axioms)
