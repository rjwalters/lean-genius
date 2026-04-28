# Knowledge: erdos-512-incomplete-01

## Problem Summary

**Goal**: Fill 2 sorry gaps in the Erdős #512 Aristotle companion file.

**Current state**:
- `Erdos512Problem.lean`: 1 sorry — `L2_norm` (Parseval's theorem, line 194)
- `Erdos512Aristotle.lean`: 2 sorries — `expSumNorm_continuous` and `L1norm_le_card`

**Note**: The Aristotle file header is outdated — `L1norm_upper_bound` in the main file is
already proved (no sorry). Only `L2_norm` remains there.

## Architecture

```
expSumNorm A θ = Complex.abs (expSum A θ)
expSum A θ = A.sum (fun n => expTwoPiI (n * θ))
expTwoPiI x = Complex.exp (2 * π * x * I)
```

Already proved (no sorry):
- `expSum_bound`: |expSum A θ| ≤ A.card (triangle + |e^{2πiθ}|=1)
- `L1norm_upper_bound`: ∫₀¹ |expSum| dθ ≤ A.card (continuity + monotone integral)
- All periodic properties, norm facts, etc.

## Session 2026-04-23 — Results (Session 1)

**Outcome**: progress
**Sorries closed**: 2 (`expSumNorm_continuous`, `L1norm_le_card` in Aristotle file)

**Key proofs**:
- `expSumNorm_continuous`: standard tactic chain — `Complex.continuous_abs.comp` →
  `continuous_finset_sum` → `Complex.continuous_exp.comp` → `fun_prop`
- `L1norm_le_card`: continuity → `integrableOn_compact` → `setIntegral_mono_on` →
  `set_integral_const` with `Real.volume_Icc`
  Both proofs mirror the inline proof in `L1norm_upper_bound` (main file lines 105-131).

**Remaining**:
- `L2_norm` (Parseval): `∫₀¹ |∑_{n∈A} e(nθ)|² dθ = |A|`
  Strategy: expand via double sum + character orthogonality `∫₀¹ e^{2πikθ} dθ = [k=0]`
  This requires more Fourier analysis infrastructure in Mathlib.

## Mathlib API Notes

- `Complex.continuous_abs.comp` — continuity of complex abs composed with continuous fn
- `continuous_finset_sum` — finite sum of continuous functions is continuous
- `Complex.continuous_exp.comp` — continuity of complex exponential
- `fun_prop` — closes arithmetic continuity goals (e.g., `2 * π * ↑n * θ * I` continuous in θ)
- `ContinuousOn.integrableOn_compact` — integrable on compact interval from continuity
- `integrableOn_const.mpr (Or.inr ...)` — constant is integrable when finite measure
- `setIntegral_mono_on` — monotone integral bound
- `set_integral_const` — integral of constant = constant * volume
- `Real.volume_Icc` — volume of [a,b] = ENNReal.ofReal (b-a)
- `ENNReal.toReal_ofReal` — converts back to ℝ

## Next Steps

1. `L2_norm`: Prove ∫₀¹ |expSum A θ|² dθ = |A| via Parseval/character orthogonality
   - Key step: `∫₀¹ expTwoPiI (k * θ) dθ = if k = 0 then 1 else 0` for integer k
   - When k≠0: antiderivative is `expTwoPiI (k * θ) / (2πki)`; FTC gives (e^{2πki}-1)/(2πki) = 0
   - Need: `Complex.integral_exp` or `intervalIntegral.integral_comp_mul_right` in Mathlib
   - Then swap integral and double sum using `MeasureTheory.integral_finset_sum`

## Session 2026-04-28 (Session 2) — Stale-Metadata Audit (researcher-4)

**Mode**: REVISIT (RICH knowledge tier, score 16)
**Outcome**: COMPLETED — sorries already closed in upstream PRs; metadata reconciled

### Verification

```
Erdos512Problem.lean:    368 lines, 14 theorems, 16 defs, 2 axioms, 0 sorries
Erdos512Aristotle.lean:   77 lines,  2 theorems,  0 defs, 0 axioms, 0 sorries
```

(Counts strip block + line comments before counting `\bsorry\b` per
`feedback_lean_sorry_counting.md`.)

### Audit Trail (Upstream PRs that closed the gaps)

- **PR #12115** (`1e702aadd36`) — *Prove L2_norm (Parseval) for Erdős #512: eliminate last sorry*
- **PR #12201** (`37754b91221`) — *Fix: erdos-512 sync sorry count 2→0 (expSumNorm_sq_double proved)*

The research entry's `progressSummary` was still describing the pre-PR-#12201 state ("L2_norm
proof structured (1 sorry: normSq double-sum expansion in expSumNorm_sq_double)"). That sorry
is gone; `expSumNorm_sq_double` is now fully proved at lines 210–240 via `Complex.normSq_apply`,
`expTwoPiI_conj`, and an inner `Complex.exp_mul_I` rewrite that extracts `cos(2π(m−n)θ)`.

### Files Modified

- `src/data/research/problems/erdos-512-incomplete-01.json`
  (lineCount 245→368, sorryCount 1→0, theoremCount 10→14, defCount 8→16; phase ACT→COMPLETED;
  status active→completed; `lastUpdate` refreshed; knowledge fields rewritten to reflect closure)
- `research/problems/erdos-512-incomplete-01/knowledge.md` (this entry)
- `.lean/state/candidate-pool.json` (status `available`→`completed`; not in this branch — pool
  lives in main repo's gitignored state, updated separately)

### Remaining Mathematical Status

The two `axiom` declarations (`konyagin_theorem`, `mcgehee_pigno_smith_theorem`) remain. They
state the Littlewood conjecture itself (now a theorem, by Konyagin 1981 / McGehee–Pigno–Smith
1981). De-axiomatization would require a fresh research entry: formalize Hardy's discrete
inequality (1920) + the MPS Fourier-coefficient chain of estimates. That's a multi-session
infrastructure project, out of scope for this `incomplete-01` follow-up.

### Why This Was Worth Doing

Per `feedback_research_pool_stale_metadata.md`: stale "available" entries on already-completed
problems waste claim cycles. Pool now reflects gallery state for this entry. Continues the
recent batch (after dissection-of-cubes-oq-04, erdos-1103, erdos-1084-oq-01, erdos-263).

