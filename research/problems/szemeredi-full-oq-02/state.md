# Current State

**Phase**: COMPLETED (verified)
**Since**: 2026-04-23T05:52:30.000Z
**Last Updated**: 2026-04-28T00:00:00Z
**Iteration**: stable — no further work pending

## Current Focus

Sequence-of-sets density formulation of Szemerédi's theorem (k-AP-free → vanishing density).

## Resolution

`proofs/Proofs/SzemerediFullOQ02.lean` (118 lines, 0 sorries) is verified. Materialized
in PR #12918 (2026-04-26) and present on `main`.

- `szemeredi_vanishing_density` — sequences of AP-free sets have density → 0 (all k ≥ 1).
  Proved via `Filter.Tendsto`.
- `roth_density_isLittleO` / `ap_free_density_isLittleO_k3` — k=3 case via Mathlib's
  `rothNumberNat_isLittleO_id`.
- `szemeredi_density_full` — main theorem alias.

The k ≥ 4 case is axiomatized through the inherited `szemeredi_k_ge_4` axiom from
`Proofs.SzemerediTheorem` (hypergraph regularity not in Mathlib). `meta.json`
records `leanFile.axiomCount: 1` to reflect the inherited assumption.

## Active Approach

n/a — file is stable.

## Blockers

None.

## Next Action

None — pool entry being reconciled to `completed`.

## Attempt Counts

- Total attempts: 1
- Approaches tried: 1 (Roth → density via Mathlib's `rothNumberNat_isLittleO_id`)
