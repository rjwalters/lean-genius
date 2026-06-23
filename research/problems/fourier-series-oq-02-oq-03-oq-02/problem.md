# Problem: Sharp Constants for Analytic (Exponential) Fourier Coefficient Decay

**ID**: fourier-series-oq-02-oq-03-oq-02
**Category**: open question — sharpening
**Tractability**: moderate (2 sorries + 3 axioms remain)
**Source Proof**: fourier-series-oq-02-oq-03 (sharp constant 1/2 for Hölder)
**Tags**: analysis, fourier, complex-analysis, paley-wiener, exponential-decay

## Problem Statement

For periodic f : ℝ/Tℤ → ℂ that extends holomorphically to the strip
{z : |Im z| < δ} and is bounded there:

  |ĉ_n(f)| ≤ K · e^{-2πδ|n|/T}

What is the sharp constant K? How does it depend on f? And what's
the converse Paley-Wiener characterization?

## Context

Source proof: Sharp Constants for Hölder Decay (OQ-02-OQ-03), which
established the sharp constant 1/2 for Hölder regularity. This OQ
extends to the analytic regime where decay is exponentially fast.

## Current State

**File**: `proofs/Proofs/FourierSeriesOQ02OQ03OQ02.lean`
**Companion**: `Proofs/FourierSeriesOQ02OQ03OQ02Aristotle.lean`
**Sorries**: 2 (`exp_dominates_polynomial`, `analytic_hierarchy`)
**Axioms**: 3 (`contour_shift_decay`, `rate_is_sharp`,
              `paley_wiener_converse`)

## Key Questions

1. Can `exp_dominates_polynomial` be proved from
   `Real.tendsto_pow_mul_exp_neg_atTop_nhds`?
2. Can `analytic_hierarchy` be derived from `exp_decay_summable`
   plus `exp_dominates_polynomial`?
3. Are the three axioms (Cauchy-shift, sharpness, Paley-Wiener)
   formalizable in Mathlib's current state?
