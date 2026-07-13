# Session 3 — STATE-SYNC

**Researcher**: researcher-9
**Date**: 2026-05-17 ~03:30Z
**Type**: doc-only STATE-SYNC (no Lean changes, no PR rebase, no Docker build)
**Predecessor**: S2 PR #13616 (researcher-1, 2026-04-28T13:08Z) — reconcile
1-sorry → 0 + pool flip available → completed
**T-since-predecessor**: ~18 days, 14h

## §0. TL;DR

claim-random selected long-COMPLETED slug `erdos-512-incomplete-01`
because the live `.lean/state/candidate-pool.json` had drifted from
`status: completed` back to `status: available` post-S2. The checked-in
`research/candidate-pool.json` is correct (`completed`); only the live
state file disagrees. Ship doc-only S3 STATE-SYNC catching up 5 JSON
registry drift surfaces + state.md ledger; run
`claim-problem.sh update erdos-512-incomplete-01 completed` post-merge
to re-flip the live pool.

## §1. Pre-claim recency probe

```
gh search prs "erdos-512-incomplete-01" --repo rjwalters/lean-genius
```

Returned 5 historical PRs, most recent T-18 days:
| PR | Date | Author | Summary |
|----|------|--------|---------|
| #11876 | 2026-04-23 | early | Session 1 — prove L1norm_upper_bound |
| #11940 | 2026-04-23 | seeker | Select for full close |
| #12052 | 2026-04-23 | researcher-2 | Close 2 Aristotle sorries |
| #12115 | 2026-04-24 | researcher-3 | L2_norm (Parseval) — 1 sorry → 0 |
| #12201 | 2026-04-24 | researcher-? | Sync sorry count 2→0 (expSumNorm_sq_double) |
| #13616 | **2026-04-28** | **researcher-1** | **S2 reconcile — pool flip → completed** |

No open PRs since. No researcher PRs since 2026-04-28. The only commits
that touched the slug's files between then and now were two ACT PRs
from other slugs that incidentally re-added or modified
`src/data/research/problems/erdos-512-incomplete-01.json` via
`pnpm build` regeneration (PRs #18059 angle-trisection 2026-05-14,
#19454 sperner-ndim-mathlib 2026-05-15) — neither touched Lean source.

**Verdict**: predecessor split = pure-completion PR T-18d; no risk of
double-shipping; STATE-SYNC scope clear.

## §2. Drift inventory (5 surfaces in JSON registry)

`src/data/research/problems/erdos-512-incomplete-01.json` vs
`research/problems/erdos-512-incomplete-01/state.md`:

| # | Field | Pre-S3 (JSON) | Canonical (state.md) | Direction |
|---|-------|---------------|----------------------|-----------|
| 1 | `currentState.since` | `2026-04-23T00:00:00.000Z` (S1 start) | `2026-04-28` (S2 completion) | bump 5d |
| 2 | `currentState.iteration` | `1` | `2` (state.md) → `3` (this PR) | bump 1→3 |
| 3 | `currentState.attemptCounts.total` | `1` | `2` (state.md) → `3` (this PR) | bump 1→3 |
| 4 | `currentState.focus` | terse | extended with PR #13616 attribution | rewrite |
| 5 | `lastUpdate` | `2026-04-28` | → `2026-05-17` | bump 19d |

Top-level `phase: "COMPLETED"` and `status: "completed"` were already
canonical (no change). Top-level `started: 2026-04-23` unchanged
(historical anchor). insights[] gets a new RE-VERIFIED 2026-05-17 entry
recording leanFiles byte-stability since #12201.

## §3. Drift surfaces explicitly NOT touched

### §3.1 defCount: 9 (narrow) vs gallery 16 (broad)

`src/data/research/problems/erdos-512-incomplete-01.json` has
`leanFiles[0].defCount: 9` (matches narrow `^def ` regex).
`src/data/proofs/erdos-512/meta.json` has `definitionCount: 16` (matches
broad `^(noncomputable )?def ` regex). Both regexes give consistent
results for `Erdos512Problem.lean`:
- Narrow `^def `: 9 lines
- Narrow `^noncomputable def `: 7 lines
- Sum (= broad enrich-research regex `^(def|noncomputable def|opaque def) `): 16

This is a pre-existing convention gap. The Lean file has not been edited
since PR #12201 (2026-04-23), so this is not a recent regression.
Mechanic recent batches (#20076, #20088, #20097, etc.) explicitly leave
`defCount` unchanged when it doesn't disagree with previous canonical
value. Slug-local file (only `erdos-512-incomplete-01` references this
Lean file) → mechanic-domain to align if desired. Deferred via
state.md "Open Questions Carried Forward".

### §3.2 lineCount/theoremCount/axiomCount/sorryCount — all canonical

Re-verified against current Lean files (commands as recorded for
audit reproducibility):

```
F=proofs/Proofs/Erdos512Problem.lean
wc -l "$F"                                          # 368 ✓ (JSON+gallery)
grep -cE '^(protected |private |noncomputable )*(theorem|lemma) ' "$F"  # 14 ✓
grep -c '^axiom ' "$F"                              # 2 ✓
grep -c '\bsorry\b' "$F"                            # 0 ✓

F=proofs/Proofs/Erdos512Aristotle.lean
wc -l "$F"                                          # 77 ✓
grep -cE '^(protected |private |noncomputable )*(theorem|lemma) ' "$F"  # 2 ✓
grep -c '^axiom ' "$F"                              # 0 ✓
grep -c '\bsorry\b' "$F"                            # 0 ✓
```

All five canonical-counted fields match for both leanFiles[] entries
in the JSON registry. No mechanic-style batch fix needed.

## §4. Open PR / sibling cross-check

No open PRs against any erdos-512-incomplete-01 file. No sibling slugs
share `Erdos512Problem.lean` or `Erdos512Aristotle.lean`
(`grep -l "Erdos512" src/data/research/problems/*.json` returns only
this slug + the gallery non-research `erdos-512` slug, which references
the gallery proof from a different angle).

## §5. Infrastructure snapshot

| Gate | Status | Value | Notes |
|------|--------|-------|-------|
| G7 disk avail | 🔴 RED | 4.5 GiB | Below 5 GiB soft-floor; cross-validates with same-window sibling PRs reporting disk degradation |
| G8 Docker server | (not probed in this session) | — | Doc-only PR; no Docker needed |
| G9 .lake symlink | 🔴 RED | `proofs/.lake → proofs/.lake` (self-loop) | Pre-existing, byte-stable |
| Mathlib pin | 🟢 GREEN | `2df2f0150c…` (byte-stable) | Same SHA as cross-session siblings |

Doc-only PR — none of these gates block this STATE-SYNC.

## §6. Pool state mechanics

`bash -x .../claim-problem.sh status` confirms script reads from
`.loom/worktrees/researcher-9/.lean/state/candidate-pool.json`, which
is a symlink to the repo-root `.lean/state/candidate-pool.json`. That
live state file currently has:

```jsonc
{
  "id": "erdos-512-incomplete-01",
  "status": "available",
  "notes": "AVAILABLE",
  ...
}
```

The checked-in `research/candidate-pool.json` has:

```jsonc
{
  "id": "erdos-512-incomplete-01",
  "status": "completed",
  "notes": "COMPLETED",
  ...
}
```

Post-merge action (manual, outside the PR diff):

```
/Users/rwalters/GitHub/lean-genius/scripts/research/claim-problem.sh \
    update erdos-512-incomplete-01 completed
```

This re-flips the live state file to match the checked-in file and
prevents future claim-random rolls from selecting this slug.

## §7. Lessons / memory notes

- **Pattern reinforcement**: `_first_claim_lands_on_long_completed_slug_with_T_18d_predecessor_split`
  is the dominant match (T-18d, single completion-PR predecessor, ~5
  drift surfaces — under the 14-surface threshold but pool live state
  mismatch is the load-bearing fix). Doc-only S3 STATE-SYNC + post-merge
  pool flip is the appropriate response.
- **Live-pool vs checked-in-pool drift** is a recurring failure mode.
  The `.lean/state/candidate-pool.json` is updated by `claim-problem.sh`
  during claim/release/update, but it can drift back when a researcher
  fails to call `update completed` after their final PR merges, or when
  another process resets it. The checked-in file under
  `research/candidate-pool.json` is *also* drifted from the gold source
  in some cases — needs eventual reconcile-or-remove decision.
- **3 RED INFRA window persists** across worktrees and sessions (disk
  4.5 GiB, .lake self-loop, Docker hung in adjacent sessions per memory
  notes). Doc-only STATE-SYNC PRs are the safest unit of work in this
  regime.

## §8. PR scope (3 files, +130/-9)

1. `src/data/research/problems/erdos-512-incomplete-01.json` — 5-field
   surgical (`currentState.{since,iteration,focus,attemptCounts.total}` +
   `lastUpdate`) + 1 new `knowledge.insights[]` entry recording 2026-05-17
   re-verification.
2. `research/problems/erdos-512-incomplete-01/state.md` — iteration 2→3,
   attemptCounts.total 2→3, new "Iteration History" + "Open Questions
   Carried Forward" + "Infrastructure Notes" sections, expanded
   "Next Action" with pool-flip plan.
3. `research/problems/erdos-512-incomplete-01/sessions/session-3-state-sync.md`
   — this memo (NEW file).

No Lean source changes. No build attempted. No Mathlib rebase.
