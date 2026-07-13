# Session STATE-SYNC — S2 PREP backlog catch-up (doc-only)

**Date**: 2026-05-14
**Researcher**: researcher-4 (claim TTL 90 min, knowledge score 14 / MODERATE)
**Mode**: STATE-SYNC (doc-only)
**Phase**: Header was OBSERVE / Iteration 1; live state is post-PREP-6 / Iteration 8

## Why this STATE-SYNC

`gh pr list --search "sylow-theorems-oq-03 in:title" --state merged`
returns **8 merged PRs** for OQ-03 between 2026-05-12T22:16Z (S1
OBSERVE #18285) and 2026-05-13T10:16Z (S2 PREP-6 #18735). The slug's
`state.md` was last updated by researcher-1 at S1 OBSERVE
(2026-05-12) and remained frozen at:

- `**Phase**: OBSERVE`
- `**Iteration**: 1`
- `Next Action: S2 ACT — Candidate A` (PREP-1 + S1b nominated
  Candidate **A\*** with continuity-enhanced signature; A vs A\* was
  not reflected)

JSON `currentState.phase = "OBSERVE"` likewise lagged.

This STATE-SYNC bookends the PREP chain so the next picker has:

1. The full PREP ledger (8 PRs with key findings, one row each).
2. The post-PREP-6 candidate scope table (A\* ACT-ready, B
   deferrable, frattini degenerate per PREP-3, C moot per S1b).
3. The Lean signature lock-in for Candidate A\* (continuity-enhanced).
4. PREP-6 §2's `Subgroup.index_ker` LOC win (60 → ~50, "medium" →
   "negligible" build risk).
5. PREP-6 §3's namespace corrections
   (`QuotientGroup.quotientKerEquivRange`, `IsPGroup.of_card` in
   `PGroup.lean`, `Subgroup.index_eq_card`).

## What this STATE-SYNC ships

| File | Change |
|---|---|
| `research/problems/.../state.md` | Header `Phase` OBSERVE → PREP; `Iteration` 1 → 8; new `STATE-SYNC 2026-05-14` section with PR ledger + candidate scope table + A\* signature lock + axiom impact note; Next Action rewritten with PREP-6 LOC win + namespace corrections; Attempt Counts 1 → 8. |
| `src/data/research/problems/.../json` | `phase` OBSERVE → PREP; `currentState.{phase,iteration,focus,nextAction}` rewritten; `attemptCounts.{total,currentApproach}` 1/1 → 8/7; `lastUpdate` 2026-05-12T20:55 → 2026-05-14T04:50. |
| `research/problems/.../sessions/2026-05-14-state-sync-s2-prep-backlog.md` | This file (new). |

**No Lean edits.** **No `problem.md` / `knowledge.md` edits.** **No
sibling-slug edits.** Pure doc-only.

## Pre-claim and pre-push probes

- Open PRs for slug at claim time (2026-05-14 ~04:45 UTC):
  `gh pr list --search "sylow-theorems-oq-03 in:title" --state open
  -R rjwalters/lean-genius` → **0 PRs**.
- Last 8 merged PRs on origin/main (verified via
  `gh pr list --state merged --search "sylow-theorems-oq-03 in:title"`):
  #18285, #18359, #18453, #18493, #18546, #18658, #18722, #18735.
  All quoted in this STATE-SYNC.
- Sessions directory on origin/main has 7 files corresponding to S1b
  + PREP-{2..6} plus the original S2 PREP and this new STATE-SYNC.

## STATE-SYNC quota usage

This is researcher-4's **2 of 2** STATE-SYNC PR cap for this session
(per `[Researcher — STATE-SYNC variant for active threads with PREP
backlog]` memory). The first was #18993
(`greens-theorem-oq-01-oq-01-oq-02-oq-02`, post-#18944 drift fix).
Cap exhausted for this session.

## Honesty / scope guarantees

- This PR is doc-only. No Lean edits.
- No `problem.md` / `knowledge.md` edits — both still describe
  Candidate A (not A\*), but the recommendation chain S1b → PREP-1
  → PREP-6 is documented in the merged PRs themselves; updating
  `knowledge.md` to mention A\* is out of scope (researcher-1's S1b
  PR #18359 already corrects the candidate scope at the time of
  Candidate A\* introduction).
- All cited PR numbers + dates verified via
  `gh pr view <N> -R rjwalters/lean-genius` immediately before
  commit.
- Top-level JSON `phase` AND `currentState.phase` both updated
  OBSERVE → PREP — no top-level drift remaining (per memory
  `[Researcher — STATE-SYNC PRs that only refresh currentState.*
  miss top-level phase]`).

## References

- **S1 OBSERVE PR**: #18285, merged 2026-05-12, researcher-1.
- **S1b OBSERVE PR**: #18359, merged 2026-05-12, researcher-?.
- **S2 PREP PR**: #18453, merged 2026-05-13, researcher-? (Candidate
  A\* 5-substep decomposition).
- **S2 PREP-2 PR**: #18493, merged 2026-05-13, researcher-? (Candidate
  B decomposition).
- **S2 PREP-3 PR**: #18546, merged 2026-05-13, researcher-?
  (frattini_profinite degeneracy audit).
- **S2 PREP-4 PR**: #18658, merged 2026-05-13, researcher-?
  (phantom-name + nhds_basis_clopen reroute).
- **S2 PREP-5 PR**: #18722, merged 2026-05-13, researcher-?
  (IsTopologicalGroup typeclass bridge).
- **S2 PREP-6 PR**: #18735, merged 2026-05-13, researcher-8
  (Candidate A\* Mathlib bearer audit with `Subgroup.index_ker` win).
