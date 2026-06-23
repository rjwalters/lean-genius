# lebesgue-measure-oq-01-oq-01-oq-02

**Problem**: Can we prove that Thomae's function is continuous at every irrational and discontinuous at every rational in Lean?

## Problem Summary

Thomae's function (popcorn function) is defined as f(p/q) = 1/q for rationals in reduced form, f(x) = 0 for irrationals. The question asks to formally verify the continuity characterization: ContinuousAt f x ↔ Irrational x.

## Answer: YES — Fully Verified

The complete characterization is proved in `LebesgueMeasureOQ01OQ01OQ02.lean` (241 lines, 6 public theorems, 0 sorries, 0 axioms).

**Key theorems**:
- `thomae_discontinuous_at_rat (r : ℚ) : ¬ContinuousAt thomae (r : ℝ)`
- `thomae_continuous_at_irrational {x : ℝ} (hx : Irrational x) : ContinuousAt thomae x`
- `thomae_continuous_iff (x : ℝ) : ContinuousAt thomae x ↔ Irrational x`

## Proof Strategy

**Discontinuity at rationals**: Sequential argument using the sequence r + √2/(n+1) → r. Each term is irrational (since √2 is irrational), giving f(y_n) = 0 → 0 ≠ 1/r.den = f(r). Lean: `tendsto_nhds_unique` derives the contradiction.

**Continuity at irrationals**: Epsilon-delta using `finite_rat_bounded` (finiteness of rationals with bounded denominator in any bounded interval) and `pos_min_dist` (positive minimum distance from irrational to finite rational set). Choose N with 1/(N+1) < ε; let δ = min distance to low-denominator rationals. For |y - x| < δ: if y is irrational f(y) = 0 < ε; if y rational with denominator > N then f(y) = 1/q.den ≤ 1/(N+1) < ε.

## Key Lean Infrastructure

- `finite_rat_bounded x N`: `{q : ℚ | |q - x| ≤ 1 ∧ q.den ≤ N}` is finite via `Finset.biUnion` over denominators
- `pos_min_dist hx S`: positive minimum distance from irrational x to finite set S, proved by `Finset.induction`
- `Rat.cast_inj`: uniqueness of the classical choice in the `thomae` definition
- `irrational_sqrt_two`: √2 is irrational (for the sequential argument)

## Session 2026-05-03 (Session 1) — Gallery Entry Creation

**Mode**: FRESH
**Outcome**: COMPLETE — created full gallery entry for pre-existing Lean file

### What I Did
- Identified that `LebesgueMeasureOQ01OQ01OQ02.lean` (241 lines, 6 theorems, 0 sorries, 0 axioms) had no gallery entry
- Created `src/data/proofs/lebesgue-measure-oq-01-oq-01-oq-02/meta.json` with full mathematical documentation
- Created `src/data/proofs/lebesgue-measure-oq-01-oq-01-oq-02/annotations.json` with 8 annotations
- Created `src/data/proofs/lebesgue-measure-oq-01-oq-01-oq-02/index.ts` for gallery auto-discovery
- Updated pool entry to in-progress
- Updated research JSON to COMPLETED phase
- Created this knowledge.md

### Key Findings
- The Lean file already proved the complete continuity characterization
- No Docker build needed (proof pre-existed, pre-verified)
- One strong follow-up: Riemann integrability via Lebesgue criterion (lebesgue-measure-oq-01-oq-01-oq-02-oq-01)

### Files Modified
- `src/data/proofs/lebesgue-measure-oq-01-oq-01-oq-02/` (new directory + 3 files)
- `src/data/research/problems/lebesgue-measure-oq-01-oq-01-oq-02.json` (knowledge + phase update)
- `.lean/state/candidate-pool.json` (available → in-progress)
- `research/problems/lebesgue-measure-oq-01-oq-01-oq-02/knowledge.md` (this file)

### Next Steps
1. PR to main: gallery entry for Thomae's function continuity characterization
2. Consider follow-up: Riemann integrability of Thomae's function via Lebesgue criterion (∫₀¹ thomae = 0, proved via continuity a.e.)
