# Research State: roth-theorem-oq-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14T17:42:10-07:00
**Iteration**: 2

## Current Focus
Feasibility and approach identified (Session 1, ORIENT). Statement anchored to Mathlib
`rothNumberNat`; sibling `roth-theorem-oq-02` precedent (axiomatized Bloom–Sisask bound) noted.

## Active Approach
SURVEY/axiomatized route. The genuine Fourier/density-increment proof is blocked on missing
Mathlib infrastructure (>1000 LOC: large-spectrum estimates, Bohr sets). Realistic next unit:
M1 — state `rothNumberNat_bourgain` (`N (loglog N/log N)^{1/2}`) and prove the bridge to the
qualitative `rothNumberNat_isLittleO_id`. Requires Docker (currently down) to verify.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- Docker build environment down (cannot compile/verify Lean this session).
- A from-scratch quantitative proof needs additive-combinatorics infrastructure (large spectrum,
  Bohr sets) not in Mathlib — out of single-session scope.

## Next Action
When Docker is up: create `proofs/Proofs/RothTheoremOQ01.lean` with the M1 deliverable —
`axiom rothNumberNat_bourgain` + proved bridge lemma `… → rothNumberNat_isLittleO_id`
(mirroring the `RothTheoremOQ02.lean` axiomatized pattern). Status `axiomatized`.
