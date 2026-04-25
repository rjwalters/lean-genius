# Knowledge: erdos-1151-oq-04

## Problem Summary

**Goal**: Prove `erdos_1941_divergence` (axiom in `Erdos1151Problem.lean`) by formalizing
that the Chebyshev Lebesgue function Λₙ(cos(πp/q)) → ∞ for odd p, q, and then
constructing a continuous function whose Chebyshev interpolation diverges.

**Axiom to eliminate**:
```lean
axiom erdos_1941_divergence (p q : ℕ) (hp : Odd p) (hq : Odd q) (hq_pos : 0 < q) :
    let x := Real.cos (p * Real.pi / q)
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, M < chebyshevInterpSeq f x n
```

This says: for x = cos(πp/q), there EXISTS a continuous f such that Lₙf(x) → +∞ (full
sequence diverges to +∞, not just a subsequence).

## Architecture (Erdos1151OQ04.lean)

**Main reduction theorem** (COMPLETE, no sorry):
```
chebyshev_lebesgue_growth [sorry] + divergence_from_lebesgue_growth [sorry]
  → erdos_1941_divergence_from_growth [PROVED]
```

**Proved lemmas (no sorry)**:
- `lebesgue_upper_bound`: |Lₙf(x)| ≤ ‖f‖_∞ · Λₙ(x)
- `chebyshevInterp_add`, `chebyshevInterp_smul`: linearity
- `chebyshev_T_at_cos`: T_n(cos θ) = cos(nθ) [from Mathlib T_real_cos]
- `cos_int_pi`: cos(kπ) = (-1)^k [from Mathlib cos_int_mul_pi]
- `cos_rational_pi_at_multiples`: cos(mq·πp/q) = cos(mπp)
- `cos_rational_pi_nonzero_along_multiples`: along n = mq, cos(nπp/q) ≠ 0
- `chebyshevNode_mem_Icc`: nodes lie in [-1, 1]
- `abs_cos_int_pi_mul`: |cos(kπ)| = 1
- **chebyshevNode_is_root** (PROVED this session): T_n(cos φₖ) = 0
- **chebyshevNode_injective** (PROVED this session): Chebyshev nodes are distinct

**Aristotle companion (Erdos1151OQ04Aristotle.lean)** — all sorries CLOSED this session:
- `cos_odd_half_pi`: cos((2k+1)π/2) = 0
- `chebyshevNode_is_root`: T_n at Chebyshev nodes = 0
- `chebyshevNode_injective`: nodes are distinct
- `n_mul_chebyshevAngle`, `chebyshevAngle_pos`, `chebyshevAngle_lt_pi`, etc. [arithmetic helpers]

## Sorries Remaining (2 in main file, as of 2026-04-24)

### 1. `chebyshev_trig_sum_lb` (line 760) — HARD, strategy known
**Goal**: ∃ C₂ > 0, ∀ n ≥ 1, C₂·n·log(n+1) ≤ Σₖ sin(φₖ)/|x - cos φₖ|

**Proof strategy** (see docstring in file, ~200 lines):
- Let θ = πp/q (fixed), φₖ = (2k+1)π/(2n) (Chebyshev nodes)
- Since sin(θ) > 0 for x = cos(θ) ∈ (-1,1) and p,q odd, we have x ≠ ±1
- Nearest node k₀: choose k₀ with |φₖ₀ - θ| ≤ π/(2n)
- Lipschitz: |cos θ - cos φₖ| ≤ |θ - φₖ| (cos is 1-Lipschitz)
- Node spacing: |θ - φₖ₀₊ⱼ| ≈ j·π/n for |j| ≤ n/2
- For nodes near k₀: sin(φₖ) ≥ sin(θ)/2 (continuity of sin)
- Harmonic sum: Σⱼ₌₁^{n/2} 1/j ≥ log(n/2 + 1) by `log_add_one_le_harmonic`
- Combining: S_n ≥ (n·sin(θ)/2π)·log(n/2+1) = C₂·n·log(n+1) up to constants
- **Case x = ±1** (θ = 0 or π, sin(θ) = 0): requires separate cot argument
  - p,q both odd ⟹ cos(πp/q) = cos(odd·π/odd) ≠ ±1 for any valid p,q
  - So this case never occurs in our hypotheses — may simplify the proof

**Mathlib tools available**:
- `Real.log_add_one_le_harmonic` or `Finset.log_le_sum_one_div` for harmonic bound
- `Real.abs_cos_sub_cos_le` or manual Lipschitz via MVT
- `Real.sin_pos_of_pos_of_lt_pi` for sin(φₖ) > 0

### 2. `divergence_from_lebesgue_growth` (line 838) — OPEN, fundamental gap
**Goal**: Λₙ(x) → +∞ ⟹ ∃ continuous f, Lₙf(x) → +∞ (full sequence)

**Fundamental gap**: Banach-Steinhaus / UBP gives `∃ f continuous, lim sup_n |Lₙf(x)| = ∞`,
NOT `lim_n Lₙf(x) = +∞` (signed, full sequence).

**Lacunary construction issues**: f = Σₖ (1/k²) fₙₖ where fₙₖ chosen so Lₙₖ(fₙₖ)(x) = Λₙₖ(x).
Cross terms: Lₙₖ(fₙⱼ)(x) for j ≠ k could dominate. Need |Lₙₖ(fₙⱼ)(x)| << Λₙₖ(x)/k² for all j < k,
which requires precise control on how Chebyshev interpolation at degree nₖ sees basis functions
for nⱼ << nₖ. This is ~300+ lines of analysis.

**Recommended action**: Weaken the sorry statement to lim sup version:
```lean
-- Weaker (provable by Baire/UBP):
theorem divergence_from_lebesgue_growth' (x : ℝ) (...) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      Filter.Tendsto (fun n => ‖chebyshevInterp n f x‖) Filter.atTop Filter.atTop
-- This follows from Banach-Steinhaus directly
```
The current statement with `M < Lₙf(x)` (signed divergence) may require full lacunary argument.

## Session 2026-04-22 — Results (archived)

**Outcome**: progress  
**Sorries closed**: 5 (chebyshevNode_is_root ×2, chebyshevNode_injective ×2, cos_odd_half_pi)
**Companion file**: now 0 sorries  
**Main file**: 4 sorries → 2 sorries (sessions 5-11 progress restored in PR #12153)

## Session 2026-04-24 (this session) — Analysis

**Outcome**: documented (no proof changes)  
**Mode**: Deep analysis of 2 remaining sorries

### What I Did
- Read Erdos1151OQ04.lean lines 740–850 to understand current proof structure
- Confirmed chebyshev_lebesgue_growth is PROVED (wraps chebyshev_lebesgue_lb which uses sorry #1)
- Analyzed sorry #1 (chebyshev_trig_sum_lb): proof strategy is clear, ~200 lines, no fundamental blocks
- Analyzed sorry #2 (divergence_from_lebesgue_growth): identified fundamental gap in axiom statement
  - UBP gives lim sup = ∞, not lim = +∞ (signed)
  - Lacunary construction requires cross-term de-correlation (~300+ lines)
  - Recommended weakening the sorry to lim sup version

### Key Findings
- Proof of sorry #1 is TRACTABLE but requires careful case analysis and harmonic sum estimates
- Sorry #2 has a genuine mathematical gap: the current statement may be stronger than what UBP gives
- p, q both odd ⟹ cos(πp/q) ∉ {±1}, so the degenerate case in sorry #1 never applies
- The main theorem `erdos_1941_divergence_from_growth` is proved — only the two intermediate lemmas remain

### Next Steps
1. Attempt sorry #1 (`chebyshev_trig_sum_lb`): Use Lipschitz + harmonic sum, ~200 lines
   - Start with `have hsin_pos : 0 < Real.sin (↑p * Real.pi / ↑q)` from p,q odd hypotheses
   - Use `Finset.sum_div_le_harmonic` or manual Σ 1/j ≥ log bound
2. For sorry #2: consider weakening to lim sup = ∞ first (provable), then escalate to full divergence
3. If sorry #1 is proved, the full proof reduces to sorry #2 alone
