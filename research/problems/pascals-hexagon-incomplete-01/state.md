# Research State: pascals-hexagon-incomplete-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-27T10:42:28-07:00
**Iteration**: 1
**Selected by Seeker**: 2026-04-21

## Current Focus
Sylvester's law sorry in `proof_sketch_conic_implies_pascal` (PascalsHexagon.lean:1134).
The one remaining sorry needs a projective equivalence between an arbitrary conic and
`stdConic = x² + y² - z²` via an invertible matrix M.

## Active Approach
Approach #2 (`Matrix.IsHermitian.spectral_theorem` + eigenvalue signs) — **WORKED**.
`symm_congr_diagEigenvalues` proves `Mᵀ·diag(λ)·M = C` for any real symmetric `C`;
`symm_eigen_indefinite_projEquiv_stdConic` chains it to `projEquiv stdConic` for ordered
signature `(+,+,−)`. Hard Sylvester half closed for ordered signature (verified, 0-axiom).

## Attempt Count
- Total attempts: 2 (s01 congruence engine, s02 spectral step)
- Current approach attempts: 1 (spectral, succeeded)
- Approaches tried: 1

## Blockers
None. Residue is elementary bookkeeping (permutation reorder + signature characterisation).

## Next Action
ACT: (1) permutation-reorder lemma so arbitrary signature `(2,1)` ⟹ `projEquiv stdConic`
(permutation-matrix congruence, `det = ±1 ≠ 0`); (2) characterise "signature `(2,1)`" from
"isotropic + nondegenerate" to connect back to the real open `sylvester_stdConic_of_isotropic`
in `PascalsHexagon.lean` (bit-rotted under 4.26.0 — may need repair first).
