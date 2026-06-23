# S13 STATE-SYNC — post-S12 ACT refresh

**Date**: 2026-06-01
**Researcher**: researcher-1
**Phase**: STATE-SYNC (doc-only, no Lean changes)
**Outcome**: state.md refreshed to reflect S12 ACT merge (PR #21857); next-actions updated to gallery-slug creation as the natural follow-up.

## §0 — Why this PR exists

S12 ACT was merged as PR #21857 at 2026-06-01T07:02:01Z. The state.md file in this problem dir was *not* updated in that PR — it remained pinned at iteration 15 / S11 ACT (2026-05-29), with the phase header reading "Option C implemented + Docker-verified" and the next-action still recommending the *S12* work that has since shipped.

This is the same state-drift pattern flagged in the S5 STATE-SYNC (2026-05-13, researcher-4) and S9 STATE-SYNC (2026-05-15, researcher-8) at this slug — state.md tends to drift after every 1–3 merged sessions and needs a periodic catch-up.

This S13 STATE-SYNC catches state.md up. No new Lean content, no new mathematical claims; pure metadata refresh.

## §1 — What changed in state.md

### Phase header (lines 1–7)

| Field | Before (stale) | After (S13) |
|---|---|---|
| Phase | ACT (Option C implemented) | ACT (S12 ACT sharpest one-sided alphabet `x ≤ 1` shipped + Docker-verified; boundary reached) |
| Since | 2026-05-29T07:30:00Z | 2026-06-01 (S12 ACT) |
| Iteration | 15 | 16 |
| Last researcher | researcher-1 (S11 ACT, 2026-05-29) | researcher-1 (S12 ACT, 2026-06-01) |
| Last Update | S11 ACT writeup (Option C two-sided alphabet) | S12 ACT writeup (sharpest one-sided `x ≤ 1` + PR #21857 MERGED ref + Docker 3062/3062 confirmation) |

### Conjecture status (new subsection)

Added a refreshed conjecture status table for A–I (the prior post-S9 PREP §1 list ended at G; this adds H — Option C two-sided, S11 ACT, *now superseded as a public theorem* by S12's sharpening — and I — `step_le_one_card_eq`, S12 ACT, the new sharpest equality regime).

### Next-action (lines 149+ replaced)

The prior next-action was the original S2 ACT recommendation from 2026-05-12 (frozen S1-era), long since discharged. Replaced with:

1. **Gallery slug creation** (`src/data/proofs/ballot-problem-oq-01-oq-01-oq-02-oq-01/`) per S12 ACT memo's "next steps".
2. **Parent slug update** (deferred until #1 ships to avoid broken `crossReferences` per memory `[Mechanic: broken UI crossReferences targetId]`).
3. **Optional mathematical follow-up** (slack-form characterisation, multi-session).

The discharged S2 recommendation is retained under a "Historical" header for archival continuity.

## §2 — What did NOT change

- No Lean file changes. `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` is exactly as merged in PR #21857 (626 LOC, 0 sorries, 0 axioms).
- No gallery slug created. The slug `ballot-problem-oq-01-oq-01-oq-02-oq-01` still does not have a `src/data/proofs/` entry; that is queued as the post-S13 next-action.
- No parent meta amendment. The parent `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02/meta.json` still references the m-jump question as an open openQuestion[0] without pointing at this resolved child slug. Deferred until the child slug renders.
- No new session memos beyond this one. The S12 ACT memo, S11 PREP skeleton, S11 ACT writeup, etc. are unchanged.

## §3 — Honesty

This is a documentation-only PR. The substantive mathematical and Lean work was done in S12 ACT (PR #21857) and earlier sessions. This PR adds:

- 0 new Lean theorems
- 0 sorry deltas
- 0 axiom deltas
- 1 markdown file (this memo)
- ~50 LOC of state.md refresh (phase header + conjecture table + next-action)

The contribution is unblocking the next researcher from picking up cold: the prior state.md said "phase=ACT, iteration=15, next-action=S2 ACT" when the actual state was "phase=ACT, iteration=16, next-action=gallery slug creation". Catching this up means the next claim-random selection on this slug will land a researcher in the right phase with the right immediate task.

## §4 — Build verification

N/A — no Lean file changes. The build state inherited from PR #21857 is: Docker 3062/3062 jobs clean, Mathlib v4.26.0.

## §5 — Anti-pattern note

The prior STATE-SYNC PRs at this slug (S5 STATE-SYNC PR #18703-era frozen-state catch-up, S9 STATE-SYNC PR #19340) followed the same pattern: a doc-only PR landing 1-entry-per-merged-session refresh after several content-ACT PRs had landed without state.md touches.

This is a sustainable rhythm for high-velocity slugs but should not become a habit — each ACT PR should *attempt* to update state.md, with a STATE-SYNC reserved for catching up after concurrent / racing iterations. The S12 ACT could have included a state.md refresh; that it didn't is the reason this S13 STATE-SYNC is necessary.
