# Research State: fundamental-theorem-calculus-oq-01-incomplete-01

## Current State
**Phase**: ORIENT (ready for ACT)
**Path**: full
**Since**: 2026-05-30 (was 2026-05-28)
**Iteration**: 3

## Current Focus

Wire the **already-proved** linchpin `ac_implies_bv` (in sibling file
`Proofs/FundamentalTheoremCalculusLebesgueOQ01.lean`, 0 sorries / 0 axioms,
gallery-verified) into the parent file to discharge the
`lebesgue_ftc_differentiable` axiom.

## Active Approach

`AC → BV` already done in sibling. Remaining gap: `BV on Icc → a.e.
DifferentiableAt on Ioo`. Mathlib has the BV → a.e. DifferentiableWithinAt
result; the last bridge is upgrading within-derivative on Icc to full
derivative on the open interior Ioo.

See knowledge.md (2026-05-30 entry) for the Lean sketch and API
risk-points.

## Completed This Iteration

- **Discovery**: `ac_implies_bv` already proved in sibling file
  `FundamentalTheoremCalculusLebesgueOQ01.lean` (gallery
  `fundamental-theorem-calculus-oq-01-oq-01`, status `verified`).
- **Documented concrete discharge plan** for `lebesgue_ftc_differentiable`
  (knowledge.md, with Lean code sketch + API placeholders to confirm
  under Docker).
- **Verified parent unchanged**: 311 lines, 2 axioms (`lebesgue_ftc_differentiable`,
  `lebesgue_ftc_integral`), 1 sorry (`cantor_function_not_ac`).

## Prior Iteration Notes (preserved)

- Added `ac_implies_continuousOn` (AC ⟹ `ContinuousOn`) — verified.
- Added `ac_on_subinterval` (AC localizes to subintervals) — verified.
- Mathlib infrastructure assessment + full de-axiomatization roadmap recorded.

## Attempt Count
- Total attempts: 1 (prior session helper-lemma adds)
- Current approach attempts: 0 (this session was discovery-only)
- Approaches tried: 0

## Blockers
- **Docker required**: Mathlib source is not on the host filesystem
  (self-referential `proofs/.lake` symlink); Mathlib lives only in the
  Docker build volume. The BV → a.e. differentiable Mathlib name must
  be grepped at build time before the discharge proof can be committed.

## Next Action

ACT phase:
1. Bank a clean baseline Docker build of the parent unchanged.
2. Add `import Proofs.FundamentalTheoremCalculusLebesgueOQ01` to the parent.
3. Replace `axiom lebesgue_ftc_differentiable` with a theorem whose
   body uses `FTCLebesgueACImpliesBV.ac_implies_bv` then Mathlib's
   BV-a.e.-differentiable lemma; see knowledge.md sketch.
4. Build; iterate on Mathlib API names until green.
5. Expected delta: parent axiomCount 2 → 1; status stays `axiomatized`
   (`lebesgue_ftc_integral` axiom remains, plus the Cantor sorry).
