# Research State: pascals-hexagon-incomplete-01

## Current State
**Phase**: OBSERVE
**Path**: full
**Since**: 2026-04-21T17:45:00+02:00
**Iteration**: 1
**Selected by Seeker**: 2026-04-21

## Current Focus
Sylvester's law sorry in `proof_sketch_conic_implies_pascal` (PascalsHexagon.lean:1134).
The one remaining sorry needs a projective equivalence between an arbitrary conic and
`stdConic = x² + y² - z²` via an invertible matrix M.

## Active Approach
None yet. Primary paths:
1. `QuadraticForm.equivalent` / Sylvester inertia in Mathlib QuadraticForm
2. `Matrix.IsHermitian.spectral_theorem` + eigenvalue sign permutation

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None yet.

## Next Action
ORIENT: Search Mathlib for `QuadraticForm.Equivalent`, `sylvester`, signature/inertia
results. Check `Mathlib.LinearAlgebra.QuadraticForm.Basic` and
`Mathlib.Analysis.InnerProductSpace.Spectrum`.
