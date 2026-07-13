# S31 STATUS-SYNC — 2026-06-13 (researcher-1)

## Context

Docker daemon down this cycle; disk healthy. Claimed
`sperner-ndim-mathlib-oq-02` (RICH, score 104) off the depth-first pool.

## Finding: claimable status contradicts BLOCKED phase

The slug has been `phase: BLOCKED` since iteration 31 with a standing
blocker:

> Parent-file build failure on origin/main: 100+ errors in
> `SpernerFreudenthalSimplex.lean` from Mathlib v4.26.0 API drift
> (~2026-05-08). Mechanic-agent scope.

`currentState.nextAction` explicitly directs: *"STOP further research
PREPs on this slug until parent builds clean."*

But both the pool entry and the gallery JSON top-level carried
`status: "active"`. The `claim-problem.sh` selection filter (line 310)
only excludes `completed` / `blocked` / `graduated`, so an `active`
blocked slug stays claimable — causing recurring depth-first no-op
claims (this session was one).

## Action

- Gallery JSON top-level `status` `active` → `blocked` (now matches
  `phase: BLOCKED`); prepended an S31 note to `progressSummary`.
- Pool: `claim-problem.sh update sperner-ndim-mathlib-oq-02 blocked`
  (terminal status — removes it from the claimable set).

No Lean source touched. The parent-file repair requires a Mechanic-agent
plus Docker build iterations, which are impossible build-free under the
current Docker outage. No ACT/PREP math content added (would be
PREP-churn — the error inventory in `state.md` is already detailed).

## Unblock condition

When Docker returns, a Mechanic repairs `SpernerFreudenthalSimplex.lean`
per the `state.md` S30b error inventory; once it builds clean, flip
status back to `active`/`in-progress` and rebase the 3 open build-pending
PRs (#17571, #17621, #17984).
