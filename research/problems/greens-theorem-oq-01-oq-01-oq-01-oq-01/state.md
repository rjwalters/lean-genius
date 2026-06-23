# Research State: greens-theorem-oq-01-oq-01-oq-01-oq-01

## Current State
**Phase**: AUDIT-FAILED — build broken on origin/main against Mathlib v4.26.0 SHA `2df2f0150c…` (researcher-1, 2026-05-31).  Slug was previously marked COMPLETED but the Lean file fails to compile (15+ errors: renamed Mathlib symbols, tactic failures, type mismatches).  Pending Mechanic repair sweep.
**Path**: full
**Since**: 2026-05-31 (audit failure discovered; slug was COMPLETED 2026-05-07 → 2026-05-30 per stale assumption)
**Iteration**: 6 (S5 STATE-SYNC catch-up → **S6 AUDIT-FAILURE**)

## ⚠ AUDIT FAILURE (S6, researcher-1, 2026-05-31)

The intended task was a deferred docstring cleanup (the only outstanding
follow-up per S5).  Docker-verify of the (trivial) comment edit instead
surfaced that `proofs/Proofs/GreensTheoremOQ01OQ01OQ01OQ01.lean`
**does not compile** on current Mathlib v4.26.0:

- ~5 unknown constants: `Continuous.prod_mk`, `Filter.eventually_of_forall`,
  `Equiv.swap_symm`, `Equiv.swap_apply_of_ne`, etc. (renamed in current Mathlib).
- ~6 tactic / unification failures: rewrite pattern mismatches, unsolved goals,
  type mismatches.
- ~5 `linter.unusedSimpArgs` warnings now treated as errors in v4.26.0.
- 1+ cascade errors (e.g. `swap01_cons_eq` reported as "unknown identifier"
  downstream).

The file's source has 0 `axiom` declarations and 0 `sorry` literals (the
structural fields in `meta.json` are accurate), but it **fails machine-checking**
under the pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**Gallery overclaim**: `src/data/proofs/greens-theorem-oq-01-oq-01-oq-01-oq-01/meta.json`
currently says `status: "verified"`, but a `verified` claim requires successful
machine-checking, not just absence of `sorry`/`axiom` literals (per `CLAUDE.md`
axiom-integrity policy).  This PR documents the gap but does **not** flip the
gallery status — that's an auditor's call.

See `sessions/2026-05-31-audit-finding-build-broken.md` for the full error
list, categorisation, and recommended follow-ups.

**Recommended next steps** (out of scope for this PR):
1. **Mechanic sweep** of `GreensTheoremOQ01OQ01OQ01OQ01.lean` for v4.26.0
   API drift (rename sweeps + tactic repairs).  Estimate: 1–3 sessions.
2. **Sibling audit** of parent file `Proofs.GreensTheoremOQ01OQ01OQ01`
   for parallel drift.
3. **Gallery flip**: once repaired, re-Docker-verify and reaffirm `verified`;
   if axiomatisation is taken as a fallback, flip slug to `axiomatized`.

This PR ships only documentation updates — no Lean source changes, no
gallery `meta.json` changes.

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
