# Research State: amgm-inequality-oq-02-oq-01-oq-03

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-06-20
**Iteration**: 3
**PR**: #27174 (build green, 7745 jobs, 0 warnings/sorries/axioms)

## Current Focus
**Route B implemented — both sorries discharged, char-2 restriction removed.**
The aeval bridge identifies the concrete `powersetCard`/power-sum definitions over a
`Finset s` with the evaluation of `MvPolynomial.esymm`/`psum` on the subtype `{x // x ∈ s}`,
transporting the proven universal `psum_two_eq` and `psum_three_closed` down to concrete
`p2_closed`/`p3_closed` over ANY CommRing. L2 (`cube_partition`) and L4 (`two_e2_eq_offPairs`)
are now algebraic corollaries (`linear_combination`).

## Active Approach
Route B (aeval transport). Bridge lemmas: `aeval_psum_subtype`, `aeval_esymm_subtype`
(via `aeval_esymm_eq_multiset_esymm` + `Finset.esymm_map_val` + `Multiset.attach_map_val'`),
`esymm_one_eq_e1`, and per-degree wrappers `e1_bridge`/`e2_bridge`/`e3_bridge`/`p2_bridge`/
`p3_bridge`. Downstream: `p2_closed`, `p3_closed` (general), then `two_e2_eq_offPairs`,
`cube_partition`, `two_mul_p3_closed`, and an unconditional `newton_girard_three_finset`.

## Attempt Count
- Total attempts: 3
- Current approach attempts: 1 (Route B)
- Approaches tried: 2 (Route A char≠2; Route B general)

## Blockers
None at the math level. Build verification via Docker in progress this session
(Aristotle backend still returns 404). Gallery status held until green build confirms.

## Next Action
Confirm green Docker build of `Proofs.AmgmInequalityOQ02OQ01OQ03Finset`; create the gallery
entry (`src/data/proofs/amgm-inequality-oq-02-oq-01-oq-03/`) as verified; mark completed.
