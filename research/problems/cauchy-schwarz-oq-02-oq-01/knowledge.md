# cauchy-schwarz-oq-02-oq-01: Parseval's Identity

## Problem Summary

Formalize Parseval's identity: ∑|ĉₙ(f)|² = ‖f‖²_{L²} for Fourier coefficients.
Follow-up to CauchySchwarzOQ02 (Hölder/L² theory).

## Session 2026-04-03 (Session 1) - Initial Formalization

**Mode**: FRESH
**Outcome**: progress (10 theorems, 1 sorry)

### What I Did
- Created `proofs/Proofs/CauchySchwarzOQ02OQ01.lean` with 10 theorems
- Built successfully with Docker (only 1 sorry warning)
- Created gallery data in `src/data/proofs/cauchy-schwarz-oq-02-oq-01/meta.json`
- Key insight: Parseval as limit of Pythagorean theorem for finite orthonormal sums

### Key Findings
- `hasSum_sq_fourierCoeff` gives HasSum form: ∑|ĉₙ|² sums to ∫|f|²dμ (not ‖f‖² directly)
- `tsum_sq_fourierCoeff` gives the tsum form directly
- `orthonormal_fourier` proves Fourier monomials are orthonormal
- `hasSum_fourier_series_L2` gives L² convergence
- Completeness (zero-kernel) proved elegantly via Fourier series uniqueness
- `fourier_pythagorean_partial` has 1 sorry (HARD: orthonormal system norm-sum)

### Files Modified
- `proofs/Proofs/CauchySchwarzOQ02OQ01.lean` (created, 198 lines, 10 theorems, 1 sorry)
- `src/data/proofs/cauchy-schwarz-oq-02-oq-01/meta.json` (created)
- `.lean/state/candidate-pool.json` (status → in-progress)

### Next Steps
- Prove `fourier_pythagorean_partial` without sorry (submit to Aristotle: HARD classification)
- Prove inner product form: ⟪f,g⟫ = ∑ ĉₙ(f)·conj(ĉₙ(g)) (uses lp.inner_eq_tsum)
