# Research State: ramsey-r4k-extensions-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-03
**Iteration**: 8 (PART VIII)

## Current Focus
Deletion/alteration method as the elementary probabilistic upgrade that STRICTLY
beats the sharp union bound at small k (where the symmetric LLL of this entry does
not). Added `deletionBound`, `ramsey_deletion_bound`, `unionBound_caps_at_17_for_K6`,
`deletion_no_mono_K6` to `RamseyR4kExtensionsOQ03Deletion.lean`.

## Active Approach
Concrete crossover witnesses via kernel `decide` on ℕ (axiom-free). k=6 discharged as
theorem (R(6,6)>18 vs union bound's 17); k=7 (R(7,7)>29 vs 27) kept as prose remark
because C(30,7)≈2M makes decide impractical.

## Attempt Count
- Total attempts: 8
- Current approach attempts: 1
- Approaches tried: LLL parameters, dependency-degree bound, LLL vs union bound
  identity, honest union-bound comparison (PART VII), deletion method (PART VIII)

## Blockers
- **ENV**: host disk 100% full; Docker mathlib-cache decompress fails (ENOSPC). This
  session's additions are Python-verified + hand-audited but NOT machine-built. Needs
  CI/deployer build (once disk is reset) to confirm green.
- **MATH**: `SymmetricLLLForRamsey` full formalization (>1000 lines, measure theory) —
  the sole remaining non-Mathlib ingredient. Left as explicit hypothesis.

## Next Action
Once the disk-full env blocker is cleared, build `Proofs.RamseyR4kExtensionsOQ03Deletion`
and confirm `deletion_no_mono_K6` / `unionBound_caps_at_17_for_K6` verify with
`#print axioms` = propext/Classical.choice/Quot.sound only.
