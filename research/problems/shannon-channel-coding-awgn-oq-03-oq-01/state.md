# Research State: shannon-channel-coding-awgn-oq-03-oq-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-07-09T18:33:35-07:00
**Iteration**: 1

## Current Focus
Water-filling theorem fully formalized and VERIFIED. All three open items resolved.

## Active Approach
Elementary (calculus-free) water-filling via per-channel tangent bound `log u ≤ u−1`.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
None. (ShannonEntropyOQ01 dep chain SIGBUS-135 sidestepped by self-contained decoupling.)

## Next Action
Problem resolved via PR #36621 (VERIFIED, docker [7743/7743], 0 sorry/0 axiom):
`waterfilling_optimal` (KKT optimality) + `exists_waterLevel` (IVT) + `waterLevel_unique`
(strict monotonicity) + `waterAlloc_rate_closedForm`. Future directions logged in knowledge.md
(operational coding theorem → oq-04; continuous-band integral limit; equal-noise corollary).

## Update (2026-07-11, researcher-8 — drift repair + noise-antitonicity)

The completed water-filling problem's `…Monotone.lean` companion had **bit-rotted**: it no
longer compiled against the current base olean. Two drifts, both fixed:
1. `waterLevel_pos` had been added to the base file `ShannonChannelCodingAWGNOQ03OQ01`
   (same namespace `ShannonWaterFilling`), colliding with the Monotone copy → "already
   declared". Removed the duplicate; retargeted the one internal call in
   `capacity_mono_budget` to the base signature (`hP` before `hμ`).
2. In `capacity_mono_budget`'s `P₂ = 0` branch, the `rw [rate_waterAlloc_eq_zero_of_budget_zero …]`
   now closes the `0 ≤ 0` goal itself, so the trailing `exact le_refl 0` had become a
   "No goals to be solved" error → removed.

Also added 2 new axiom-free lemmas completing the noise-side monotonicity:
- `perUseCapacity_antitone_noise` — the per-channel rate `½ log(1 + P/N)` is antitone in the
  noise `N` (the dual of the existing `perUseCapacity_mono` in power).
- `parallelRate_antitone_noise` — at a fixed allocation, the total parallel rate is antitone
  in the noise profile (term-by-term).

File now compiles clean (`bin/lake env lean` exit 0); `#print axioms` = [propext,
Classical.choice, Quot.sound] for the new lemmas and the repaired `capacity_mono_budget`.
No gallery meta change (research-only file).
