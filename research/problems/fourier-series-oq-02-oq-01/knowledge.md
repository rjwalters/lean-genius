# fourier-series-oq-02-oq-01: Riemann-Lebesgue via Parseval's Identity

**Status**: COMPLETED (0 sorries, 0 axioms)
**Phase**: COMPLETED
**File**: `proofs/Proofs/FourierSeriesOQ02OQ01.lean`

## Problem Statement

Open Question OQ-02-OQ-01: Can `riemannLebesgue_of_holder` (from FourierSeriesOQ02) be proved
directly from Mathlib's L² theory (Parseval's identity) instead of via explicit Hölder decay bounds?

**Answer**: YES.

## Session 2026-04-21 (Session 1) - Parseval-Based Alternative Proof

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Read the parent proof in `FourierSeriesOQ02.lean` to understand the original Hölder decay approach
2. Identified the Parseval-based alternative pathway:
   - Hölder → continuous → L² (via `ContinuousMap.toLp`)
   - Parseval: `hasSum_sq_fourierCoeff` gives `∑‖ĉₙ‖² < ∞`
   - Summable → `tendsto_cofinite_zero`
   - Apply `Real.sqrt` composition to convert `‖ĉₙ‖² → 0` to `‖ĉₙ‖ → 0`
   - Use `Metric.tendsto_nhds` to convert to the final convergence claim
3. Located key Mathlib APIs:
   - `ContinuousMap.toLp`: `Mathlib/MeasureTheory/Function/LpSpace/ContinuousFunctions.lean`
   - `hasSum_sq_fourierCoeff`: `Mathlib/Analysis/Fourier/AddCircle.lean`
   - `Summable.tendsto_cofinite_zero`: from `@[to_additive]` of `Multipliable.tendsto_cofinite_one`
4. Wrote complete proof file `proofs/Proofs/FourierSeriesOQ02OQ01.lean` (namespace `FourierHolderParseval`)

### Key Findings

- `ContinuousMap.toLp` requires `[CompactSpace α]`, `[IsFiniteMeasure μ]`, `[Fact (1 ≤ p)]` — all
  satisfied automatically for `AddCircle T` with `haarAddCircle`
- `hasSum_sq_fourierCoeff` is the Parseval identity directly for `Lp ℂ 2 haarAddCircle`
- The Fourier coefficient equality between the `Lp` embedding and the original function follows from
  `ContinuousMap.coeFn_toLp` a.e. equality via `integral_congr_ae`
- `Summable.tendsto_cofinite_zero` gives the cofinite convergence of terms directly
- The sqrt composition argument: `Real.continuous_sqrt.continuousAt.tendsto.comp hSq_zero` plus
  `Real.sqrt_sq (norm_nonneg _)` gives norm convergence from squared-norm convergence
- Final step uses `Metric.tendsto_nhds` + `Real.norm_of_nonneg (norm_nonneg _)`

### Files Modified

- `proofs/Proofs/FourierSeriesOQ02OQ01.lean` (new file)
- `proofs/Proofs.lean` (added `import Proofs.FourierSeriesOQ02OQ01`)

### Mathematical Insight

The Parseval approach reveals that Riemann-Lebesgue for L² is simply "summable series have terms → 0".
The Hölder assumption only ensures L² membership; the actual convergence comes entirely from L²
structure. This proof is shorter and more general (works for all L² functions, not just Hölder).

### Comparison with OQ-02

| Approach | Technique | Strength |
|----------|-----------|----------|
| OQ-02 (Hölder decay) | Explicit bound ≤ M/(2\|n\|^α) | Quantitative rate |
| OQ-02-OQ-01 (Parseval) | L² embedding + Parseval | Shorter, more general |

### Next Steps

None — proof is complete. Potential follow-ups:
- OQ-02-OQ-02: Does the Parseval approach generalize to BV functions?
- Does the L²-membership approach give sharp bounds on convergence rate?
