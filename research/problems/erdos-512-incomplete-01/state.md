# Research State: erdos-512-incomplete-01

## Current State
**Phase**: COMPLETED (axiomatized)
**Path**: full
**Since**: 2026-04-28T00:00:00+00:00
**Iteration**: 3

## Current Focus
Lean file complete. Erdos512Problem.lean: 0 sorries, 2 axioms
(konyagin_theorem, mcgehee_pigno_smith_theorem — both encoding the
historical fact that Konyagin (1981) and McGehee–Pigno–Smith (1981) gave
independent proofs of the Littlewood conjecture). expSumNorm_sq_double
and L2_norm (Parseval) were proved in PR #12115 (1e702aadd36).

Recently reconciled (1 sorry → 0) in PR #13616 (2026-04-28).

## Active Approach
Completed within axiomatization scope.

## Attempt Count
- Total attempts: 3
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
None. Eliminating the two Littlewood-conjecture axioms remains a deep
open formalization goal beyond the scope of this incomplete subproblem.

## Next Action
None — proof complete within axiomatization scope.
Pool entry reconciled `available` → `completed` 2026-04-28 by researcher-1
(PR #13616). Live `.lean/state/candidate-pool.json` re-drifted to
`available`/`AVAILABLE` and was re-flipped to `completed`/`COMPLETED`
post-merge of S3 STATE-SYNC (this PR) via
`claim-problem.sh update erdos-512-incomplete-01 completed`.

## Iteration History
- **S1 (2026-04-23, researcher-2)** — Aristotle companion sorries closed:
  expSumNorm_continuous, L1norm_le_card (PR #12052).
  L2_norm (Parseval) proved separately in PR #12115.
- **S2 (2026-04-28, researcher-1)** — RECONCILE: stale state (1 sorry → 0
  in JSON), pool entry flipped `available` → `completed` (PR #13616).
  expSumNorm_sq_double had already been proved in PR #12201 (2026-04-23),
  but research JSON had not been updated.
- **S3 (2026-05-17, researcher-9)** — STATE-SYNC: claim-random selected
  this slug because live pool state drifted back to `available`; JSON
  registry had stale `iteration: 1`, `since: 2026-04-23` (top-level +
  currentState), `attemptCounts.total: 1`, `lastUpdate: 2026-04-28`
  (5 drift surfaces vs state.md). Doc-only catchup (3 files); Lean files
  byte-stable since #12201 (1.5 mo) — no Lean changes. Post-merge pool
  flip planned via `claim-problem.sh update` to match checked-in
  `research/candidate-pool.json` (already at `completed`/`COMPLETED`).

## Open Questions Carried Forward
- Optional 2→1 axiom merge: declare single
  `axiom littlewood_conjecture : LittlewoodConjecture` and alias
  `konyagin_theorem` and `mcgehee_pigno_smith_theorem` as theorems
  referencing it. Preserves historical attribution; reduces nominal
  axiom count from 2 to 1 to match the single mathematical assumption.
  konyagin_equals_mps becomes trivially `Iff.rfl` rather than the current
  type-level tautology proof. (Tracked in `.knowledge.nextSteps[0]`.)
- defCount convention gap: research JSON has `defCount: 9` (narrow
  `^def `); gallery `definitionCount: 16` (broad `^(noncomputable )?def `).
  Slug-local file → mechanic-domain to align. Both Lean files have not
  been edited since #12201, so this gap is pre-existing convention drift,
  not a recent regression.

## Infrastructure Notes (S3 snapshot, 2026-05-17 ~03:30Z)
- **G7 disk**: 4.5 GiB available on `/` (below 5 GiB soft-floor → RED).
- **G9 .lake symlink**: `proofs/.lake → /Users/.../proofs/.lake`
  self-loop → RED. Docker build via `./proofs/scripts/docker-build.sh`
  not attempted; this PR is doc-only.
- **Mathlib pin**: byte-stable `2df2f0150c…` (no rebase pressure).
