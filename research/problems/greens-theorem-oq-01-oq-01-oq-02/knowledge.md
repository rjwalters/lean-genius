# Standalone Interval Integral Swap (greens-theorem-oq-01-oq-01-oq-02)

## Problem

Does Mathlib contain (or could it be contributed) a version of `intervalIntegral_swap`
as a standalone lemma, avoiding the need for each application to reimplement the Ioc/Icc
conversion?

## Status

**COMPLETE: 0 sorries, 0 axioms, verified.**

---

## Session 2026-05-06 (Session 1) — Gallery Entry Created

**Mode**: FRESH
**Outcome**: completed — 4 theorems, 0 sorries, 0 axioms

### What I Did
- Found existing untracked Lean file `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` (240 lines)
  previously created by another session but never committed
- Verified 0 sorries and 0 axioms (no `sorry` or `axiom ` in file)
- Created gallery entry: meta.json, annotations.json, index.ts
- Added import to Proofs.lean manifest
- Added listing to listings.json
- Updated pool to mark in-progress, created PR

### Key Findings
- **Answer is NO** — Mathlib (as of rev 2df2f015) has no `intervalIntegral_swap` standalone
- The Ioc/Icc bridge is the obstruction: `integral_integral_swap` uses Ioc product measures,
  while integrability naturally comes in Icc form; `Measure.restrict_mono Ioc_subset_Icc_self` bridges this
- General case (any a,b,c,d) reduces to ordered case via `integral_symm` sign flips (4 subcases)
- For continuous f: `isCompact_uIcc.prod + ContinuousOn.integrableOn_compact` gives everything for free

### Files Modified
- `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` (committed from untracked)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/greens-theorem-oq-01-oq-01-oq-02/` (new gallery entry)
- `src/data/proofs/listings.json` (new listing entry)
- `.lean/state/candidate-pool.json` (status: completed)

### Next Steps
- Mathlib contribution: propose `MeasureTheory.intervalIntegral.swap` to mathlib4
- n-dimensional generalization: ∫ x₁ in a₁..b₁, … ∫ xₙ in aₙ..bₙ, f using n-dim Fubini
