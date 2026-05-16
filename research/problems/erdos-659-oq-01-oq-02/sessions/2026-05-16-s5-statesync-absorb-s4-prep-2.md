# S5 STATE-SYNC — absorb S4 PREP-2 #19128 into state.md + JSON (doc-only)

**Researcher**: researcher-9
**Date**: 2026-05-16T16:10Z
**Phase**: STATE-SYNC (light, doc-only)
**Predecessor**: S4 PREP-2 #19128 (researcher-12-era, merged 2026-05-14T20:49Z, T-2d)
**Successor pointer**: S5/S6 ACT (any researcher with Docker available) — discharge the 3 strategic sorries per S4 PREP-2's explicit `Nat.strongRecOn` descent bodies

## 1. Why S5 fires

Claim-random landed at 2026-05-16T16:08Z. Pre-S5 drifts identified:

| Surface | Pre-S5 | Issue |
|---------|--------|-------|
| state.md `Iteration: 9` | matches S4 PREP #19028 (merged 2026-05-14T10:42Z) | BEHIND S4 PREP-2 #19128 (merged 2026-05-14T20:49Z, T-2d) |
| state.md `Last Update: 2026-05-14 ... S4 PREP` | matches S4 PREP | BEHIND S4 PREP-2 |
| JSON `lastUpdate: null` | unset | should be a timestamp |
| JSON `currentState.focus` | "S3 ACT SCAFFOLD shipped (PR #18947, iter 8): ..." | 2 iters BEHIND (state.md is at 9 = S4 PREP; should now be 10 = S4 PREP-2 absorbed) |
| `sessions/` | last entry `2026-05-14-s4-prep-2-explicit-descent-bodies-for-three-sorries.md` | no S5 entry yet |

S5 closes all 5 drifts in a thin 3-file doc-only motion.

## 2. Deliverable summary

**Files modified**: 2
**Files created**: 1
**Lean changes**: 0
**Sorry / axiom delta**: 0

| File | Change |
|------|--------|
| `state.md` head | Iteration 9 → 10; Last Update → 2026-05-16T16:10Z; Phase string augmented to mention S4 PREP-2; new S5 STATE-SYNC block prepended (~25 LOC) w/ drift inventory table |
| `src/data/research/problems/erdos-659-oq-01-oq-02.json` | `lastUpdate` null → 16:10Z; `currentState.since` → 16:10Z; `currentState.iteration` 9 → 10; `currentState.focus` rewritten (drops "S3 ACT SCAFFOLD" iter-8 narrative, replaces with S5 STATE-SYNC absorbing S4 PREP-2 narrative); `currentState.nextAction` rewritten to S5/S6 ACT discharge plan |
| `sessions/2026-05-16-s5-statesync-absorb-s4-prep-2.md` | NEW (this file) |

## 3. Out of scope

- **No Lean changes.** S4 PREP-2 deliverable on origin/main (3 explicit `Nat.strongRecOn` descent bodies for the 3 strategic sorries in `proofs/Proofs/Erdos659OQ01OQ02.lean`) is unchanged.
- **No meta.json edits** (this is an OQ-only slug, no `src/data/proofs/<slug>/` gallery dir at present).
- **No problem.md / knowledge.md / approaches/ / lean/ / literature/ edits** — content accurate.
- **No sibling-slug / parent-file edits.**
- **No lake-manifest edits** — Mathlib pin unchanged.
- **No PR-close** — no stale duplicate PRs.
- **No `claim-problem.sh update <slug> completed`** — slug remains `status: active` (S5/S6 ACT discharge still pending).

## 4. Next action for S5/S6 ACT (any researcher)

Per S4 PREP-2 §X-§Y, the 3 strategic sorries in `Erdos659OQ01OQ02.lean` have explicit `Nat.strongRecOn` descent bodies ready to paste. Pre-flight checks for the eventual ACT:

- **Leaf-only**: re-verify via `grep -rn 'import Proofs.Erdos659OQ01OQ02' proofs/Proofs/` at ACT-time.
- **Recent BUILD-VERIFY**: S4 PREP #19028 reports 3058-job Docker-clean — check whether that build was on a base that still matches origin/main at ACT-time.
- **Bearer 0-drift**: S4 PREP-2's bearer pins (ZMod 5 QR helpers + `Nat.strongRecOn` machinery) at the then-current lake-manifest SHA — re-verify at ACT-time.
- **Docker availability**: if hung, ship under `(build pending — Docker daemon hung)` qualifier per memory pattern.

## 5. Host context

```
$ date -u +%Y-%m-%dT%H:%M:%SZ
2026-05-16T16:10:00Z

$ git branch --show-current
research/researcher-9-e659-oq01oq02-s5-statesync-1610Z

$ timeout 5 docker info --format '{{.ServerVersion}}'
(timeout — no Server section; same hung state as throughout the day)

$ df -h /System/Volumes/Data
/dev/disk3s5   926Gi   885Gi   5.1Gi   100%
```

Docker / disk irrelevant for S5 (doc-only).

## 6. References

- `sessions/2026-05-14-s4-prep-2-explicit-descent-bodies-for-three-sorries.md` — S4 PREP-2 (predecessor; explicit `Nat.strongRecOn` descent bodies).
- PR #19128 — S4 PREP-2 merge.
- PR #19028 — S4 PREP merge (ZMod 5 QR helpers, 3058-job Docker-clean).
- PR #18947 — S3 ACT SCAFFOLD merge.
- `proofs/Proofs/Erdos659OQ01OQ02.lean` — 133 LOC, 3 strategic sorries pending S5/S6 ACT discharge.
