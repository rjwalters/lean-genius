# Research State: amgm-inequality-oq-03-oq-01-oq-02

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-06-24
**Iteration**: 2

## Current Focus
Done. Single Mathlib-idiom theorem `Real.rpow_mean_le_rpow_mean` proves the
generalized mean inequality for ALL nonzero real p ≤ q, on the raw expression
`(∑ wᵢzᵢ^p)^(1/p)` — the gap recorded in the Mathlib.Analysis.MeanInequalitiesPow TODO.

## Active Approach
Sign trichotomy: Jensen (positive), duality M_p(z)=M_{-p}(z⁻¹)⁻¹ (negative),
geometric-mean bridge G=∏zᵢ^wᵢ (sign-crossing).

## Outcome
- File: proofs/Proofs/AmgmInequalityOQ03OQ01OQ02.lean (254 lines, 1 thm + 10 lemmas + 1 def)
- 0 axioms (propext/Classical.choice/Quot.sound only), 0 sorries — verified.
- Gallery entry: src/data/proofs/amgm-inequality-oq-03-oq-01-oq-02/

## Next Action
None — completed. A genuine upstream Mathlib PR would add the equality
characterization (M_p = M_q ↔ all zᵢ equal) and NNReal/ENNReal versions.
