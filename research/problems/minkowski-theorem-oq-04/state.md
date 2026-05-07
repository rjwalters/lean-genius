# Research State: minkowski-theorem-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-05-07T20:08:05Z
**Iteration**: 4

## Current Focus

Closing the two sorries in `minkowski_from_blichfeldt` (the half-scaling
reduction of Minkowski to Blichfeldt). After this session: 0 sorries on the
proof path; 2 axioms remain (`blichfeldt_volume_partition`,
`blichfeldt_general`).

## Active Approach

Half-scaling sorries closed via:
- Sorry 1 (measurability of T = (1/2)·s): rewrite `(2:ℝ)⁻¹ • s` as preimage
  under doubling, then `MeasurableSet.preimage` with `measurable_const_smul`.
- Sorry 2 (vol(T) > 1 from vol(s) > 2ⁿ): `Measure.addHaar_smul` for the
  scaling identity, then ENNReal arithmetic via `mul_lt_mul_left` and
  `(2⁻¹)ⁿ · 2ⁿ = 1`.

Required: `open Pointwise` to expose the `Set.SMul` instance.

## Attempt Count
- Total attempts: 4
- Current approach attempts: 1
- Approaches tried: 1 (preimage-rewrite for measurability, addHaar_smul for volume)

## Blockers

None for the half-scaling reduction; 2 axioms remain that capture standard
Mathlib measure-theory facts:
- `blichfeldt_volume_partition` — `IsAddFundamentalDomain.lintegral_eq_tsum`
  applied to `Set.indicator s 1` (one-shot Mathlib invocation).
- `blichfeldt_general` (k≥1) — covering-count averaging argument; Lebesgue
  integration of c(z) = #{v | z+v ∈ S} over the fundamental domain.

## Next Action

Eliminate `blichfeldt_volume_partition` axiom: invoke
`(stdLattice_isAddFundamentalDomain n).lintegral_eq_tsum` on the indicator
function `Set.indicator s (fun _ => (1 : ℝ≥0∞))`. Each summand
`∫⁻ z in F, 1_S(z + g) dz` collapses to `volume {z ∈ F | z+g ∈ S}` by the
indicator-of-set identity for measure.
