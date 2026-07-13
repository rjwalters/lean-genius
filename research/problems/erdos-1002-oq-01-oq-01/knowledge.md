# Erdős #1002 OQ-01-OQ-01 — Weyl Equidistribution

## Problem Summary

Prove Weyl equidistribution for continuous periodic functions and the
fractional part average result (1/n)·S(α,n) → 0 for irrational α.

**File**: `proofs/Proofs/Erdos1002OQ01OQ01.lean`
**Status**: 1 sorry, 1 axiom, 18 theorems/lemmas (643 lines)

## Session 2026-04-12 (Session 4) — Fill 3 sorries

**Mode**: REVISIT
**Outcome**: progress — eliminated 3 of 4 sorries

### What I Did

- **continuous_comp_fract integer case** (was sorry at line 325):
  Proved that `f ∘ Int.fract` is continuous at integer points when `f(0) = f(1)`.
  Used ε-δ via `Metric.continuousAt_iff`:
  - Get δ₁ from f continuous at 0 (handles right-approach: fract(y) → 0⁺)
  - Get δ₂ from f continuous at 1 (handles left-approach: fract(y) → 1⁻)
  - Take δ = min(δ₁, δ₂, 1), case split y ≥ x vs y < x
  - Floor manipulation: ⌊y⌋ = ⌊x⌋ for y ∈ [x, x+1), ⌊y⌋ = ⌊x⌋-1 for y ∈ (x-1, x)

- **deviation_sandwich integral bound g_up** (was sorry at line 439):
  Proved `∫₀¹ sandwichUpCore δ (fract x) dx ≤ ε`:
  1. Replace fract by id on [0,1] via `integral_congr` (fract(x) = x for x ∈ [0,1))
  2. Decompose: sandwichUpCore = (1/2-x) + max(0, x-(1-δ))/δ
  3. ∫₀¹ (1/2-x) = 0 via integral_const + integral_id
  4. ∫₀¹ bump ≤ δ ≤ ε via integral_mono (bump ≤ 1 on support of width δ)

- **deviation_sandwich integral bound g_lo** (was sorry at line 441):
  Symmetric argument for lower bound.

### Key Findings

- On [0,1], f(fract(x)) = f(x) for ALL x (not just a.e.) when f(0)=f(1):
  at x=1, fract gives 0 but f(0)=f(1) so values agree.
- Floor equality proofs use: `Int.floor_le`, `exact_mod_cast`, `Int.le_floor.mpr`, omega
- `Int.fract_eq_self.mpr` for x ∈ [0,1) and `Int.fract_one` for x = 1

### Files Modified

- `proofs/Proofs/Erdos1002OQ01OQ01.lean` (312→643 lines, 4→1 sorries)
- `src/data/research/problems/erdos-1002-oq-01-oq-01.json` (knowledge updated)

### Next Steps

- **equidist_approx** (sole remaining sorry): Connect `span_fourier_closure_eq_top`
  on `AddCircle 1` to concrete uniform approximation of ℝ→ℝ periodic functions
  by trig polynomials, then show irrational rotation averages converge via
  `weyl_cesaro_zero`. Requires ~200 lines of Fourier analysis formalization.
- **Build verification needed**: Docker was unavailable; proofs need `docker-build.sh` check.
