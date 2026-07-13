# Research State: minkowski-theorem-oq-04-oq-02

## Current State
**Phase**: COMPLETE
**Path**: full
**Since**: 2026-07-01
**Iteration**: 2

## Current Focus
Delivered the covolume-threshold forms of Blichfeldt and Minkowski for an arbitrary
full-rank lattice. Verified, 0-axiom, 0-sorry.

## Active Approach
Approach 1 (re-parametrize the parent's Path A) — but discovered the parent ALREADY
contains the lattice-parametric engine `blichfeldt_general_lattice` (verified, 0-axiom,
threshold in raw ℝ≥0∞ fundamental-domain volume). The genuine gap was the covolume-facing
restatement + the general-lattice Minkowski convex body theorem. Built those as a child
file importing the parent.

## Deliverables (Proofs/MinkowskiTheoremOQ04OQ02.lean, 8 theorems / 206 lines)
- `covolume_eq_toReal_volume_fundamentalDomain` — covol Λ = (volume F).toReal bridge
- `natCast_mul_volume_fundamentalDomain` — (k:ℝ≥0∞)·volume F = ofReal(k·covol Λ)
- `blichfeldt_general_lattice_covolume` — Blichfeldt, vol(S) > k·covol(Λ)
- `blichfeldt_basic_lattice`, `blichfeldt_basic_lattice_covolume` — k=1 corollaries
- `minkowski_lattice` — general-lattice Minkowski, threshold 2ⁿ·volume F
- `minkowski_lattice_covolume` — general-lattice Minkowski, threshold 2ⁿ·covol(Λ)

Directly answers open question #2 of parent minkowski-theorem-oq-04.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
None.

## Next Action
Complete: PR opened, gallery entry added. Release claim.
