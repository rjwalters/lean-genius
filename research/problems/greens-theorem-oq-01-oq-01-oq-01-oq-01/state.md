# Research State: greens-theorem-oq-01-oq-01-oq-01-oq-01

## Current State
**Phase**: COMPLETED (STATE-SYNC catch-up applied 2026-05-16)
**Path**: full
**Since**: 2026-05-07T00:00:00+03:00
**Iteration**: 5

> S5 STATE-SYNC (2026-05-16, researcher-4): doc-only catch-up after pool drift discovered
> at claim-time. Slug was fully discharged at S4 (PR #16934 retired the parent axiom on
> 2026-05-07) but candidate-pool.json still listed `in-progress` and research JSON still
> reported pre-S4 iteration/lineCount/theoremCount/axiomCount values. No Lean source
> changes; child file `GreensTheoremOQ01OQ01OQ01OQ01.lean` remains at 516 LOC / 10
> theorems / 0 axioms / 0 sorries / status verified. See
> `sessions/2026-05-16-s5-state-sync-pool-drift-catchup.md` for the per-field drift table
> and the build-inheritance argument.

## Outcome
**PROVED**: `iteratedIntervalIntegral_order_independent` from first principles, 0 sorries, 0 axioms.

## What Was Proved

- `continuous_param`: parameterized iterated integral is continuous (DCT induction on n)
- `integrable_swap_pair`: integrability for the 2-variable Fubini swap
- `swap01_cons_eq`: Fin arithmetic for the 0↔1 transposition computation
- `swap_outer_two`: Fubini swap of integration positions 0 and 1
- `iteratedIntervalIntegral_perm_tail`: inner permutation reduction (IH inside outer integral)
- `iter_integral_swap_zero`: integral identity for any transposition swap(0,k)
- `iter_integral_swap_any`: integral identity for any transposition swap(x,y)
- `iteratedIntervalIntegral_order_independent`: main theorem via swap_induction_on

## Approach
- Decomposed via `Equiv.Perm.swap_induction_on`: every permutation = product of transpositions
- Each transposition handled by `iter_integral_swap_any` (uses Fubini + IH)
- Continuity proved by DCT (`continuousAt_of_dominated_interval`, compact bound)

## Attempt Count
- Total attempts: 4 sessions
- Approaches tried: 1 (Fubini + swap decomposition — succeeded)

## Blockers
None. All sorries resolved.

## Follow-Up
- ~~oq-01: Remove redundant `axiom iteratedIntervalIntegral_order_independent` from parent
  file `proofs/Proofs/GreensTheoremOQ01OQ01OQ01.lean`.~~ **Resolved** in PR #16934
  ("retire iteratedIntervalIntegral_order_independent axiom", merged 2026-05-07):
  parent file no longer declares the axiom (verified by `grep -nE '^axiom\b'` returning
  only a docstring hit on the child file at line 513, not a real declaration).
- (Optional, deferred) Child file `GreensTheoremOQ01OQ01OQ01OQ01.lean` lines 488-513
  still carry a stale `/-- ...Status of Iteration 4...-/` docstring referencing "Remaining
  sorries (2 total)" and "Eliminates axiom once both remaining sorries are resolved" —
  both conditions are now historically satisfied. A pure-comment cleanup is safe (no
  build risk) but requires Docker re-verify per the axiom-integrity policy; host disk
  is at 100% capacity (6.9 Gi avail) so this cleanup is deferred to a future cycle
  when Docker is restored. Not blocking the COMPLETED status.

## Pool/JSON Drift Fixed in S5 (this PR)
- candidate-pool.json: `in-progress → completed` (applied locally by claim-problem.sh
  update; `.lean/state/candidate-pool.json` is gitignored — no commit needed for this).
- research JSON `currentState.iteration`: 2 → 5 (was lagging state.md by 2; now matches
  the S5 increment).
- research JSON `currentState.focus`: appended S5 STATE-SYNC summary noting pool sync,
  problem.md status sync, state.md iteration bump, and build-inheritance lineage.
- research JSON `currentState.nextAction`: `"None."` → annotated with the optional
  deferred Lean-docstring cleanup.
- research JSON `lastUpdate`: 2026-05-07T17:00Z → 2026-05-16T09:30Z (9-day refresh).
- problem.md `**Status**: Active` → `**Status**: Completed (S4 ACT PR #16934)`.

Not in this PR (already correct on origin/main HEAD `ecb47b35601`, verified via
`git show origin/main:...`):
- research JSON `leanFiles[GreensTheoremOQ01OQ01OQ01OQ01.lean]`: `lineCount: 516`,
  `theoremCount: 10`, `axiomCount: 0`, `sorryCount: 0` — all already match the Lean
  source. (A separate uncommitted edit in the main-repo working tree showed pre-fix
  values 517/4/1, but that working-tree state is not on origin/main.)
- Gallery meta.json `status: verified`, `badge: verified`, `axiomCount: 0` — accurate.
- Parent file axiom retirement — done in PR #16934.
