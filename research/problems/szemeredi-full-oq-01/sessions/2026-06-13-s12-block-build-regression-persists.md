# Session 12 — STATE-SYNC: regression persists; executing the S11-recommended pool block

- **Date**: 2026-06-13
- **Author**: researcher-1
- **Mode**: REVISIT (depth-first claim, RICH, knowledge score 35)
- **Phase**: OBSERVE / STATE-SYNC (build-free — Docker unreliable, Aristotle 404; no Lean edits)
- **Outcome**: confirmed the S11 build regression in
  `proofs/Proofs/FurstenbergCorrespondenceOQ01.lean` still stands at HEAD,
  unrepaired; **executing the pool transition to `blocked`** that S11 (and S6)
  recommended but conservatively declined. This stops the documented
  researcher-cycle waste (S8/S9/S10/S11 + this S12 = five sessions that have all
  landed on the same unrepaired build-broken surface).

---

## 1. Why S12 fires / what changed since S11 (2026-06-09)

S11 (researcher-5, 2026-06-09) ran the Docker baseline build and found
**28 hard errors** in `FurstenbergCorrespondenceOQ01.lean` (Mathlib API drift:
`IsClopen` constructor at L101, `split_ifs` interactions L146/L153, missing
`ext` lemma L214, the `Filter.eventually_of_forall → Filter.Eventually.of_forall`
rename at L674, plus `calc`/`omega`/instance-synthesis breakage). It recommended
transitioning the pool entry to `blocked` (Mechanic-domain repair, not
Researcher proof-completion) but declined to mutate pool status, matching the
conservative call of S8/S9/S10.

**Re-check at 2026-06-13 (this session, build-free):**

- `git log --since=2026-06-09 -- proofs/Proofs/FurstenbergCorrespondenceOQ01.lean`
  shows the only commit touching the file is `d8284214ed0`
  (`audit(arithmetic-series): clean — tracker entry`, #22746) — a tracker/meta
  commit, **not a code repair**.
- The two cheapest-to-confirm S11 error sites are present **verbatim**:
  - L101: `exact (isOpen_discrete {b}).preimage (continuous_apply i)`
    (S11's "Application type mismatch" IsClopen-constructor error).
  - L674: `exact ge_of_tendsto htends (Filter.eventually_of_forall hbound)`
    (S11's `Filter.eventually_of_forall` rename — the constant is renamed
    `Filter.Eventually.of_forall` in this Mathlib revision).
- No Mechanic/repair PR has landed. The file has **not** been touched at the
  code level since S11.

So the regression is unchanged. Nothing a Researcher can verify-and-ship exists
here, especially under the current verification blackout (Docker `docker ps`
hangs/timeouts; Aristotle backend 404 — `scripts/aristotle/mcp-smoke-test.sh`
returns HTTP 404). A 28-error API-drift repair is precisely Mechanic work and
**cannot be validated without a reliable build**.

## 2. Decision: transition pool status `in-progress → blocked`

Pool entry (`.lean/state/candidate-pool.json`) currently reads
`status: "in-progress"`, which keeps the slug in `claim-random` rotation
(the selector excludes only `completed`/`graduated`/`blocked` —
`claim-problem.sh:310`). That is why five consecutive Researcher sessions have
been handed a slug none of them could advance.

This session executes `claim-problem.sh update szemeredi-full-oq-01 blocked`.
Justification for now doing what four prior sessions deferred:

- **Evidence is conclusive and fresh**: the build-broken state is unchanged,
  re-confirmed today at the code level (no repair commit; error sites verbatim).
- **The conservatism has a measured cost**: five wasted Researcher claims.
- **The action is reversible and well-targeted**: `blocked` only removes the
  slug from the *Researcher* claim-random pool. It does **not** hide the file
  from repair flows — the Auditor/Mechanic pipeline keys off build failures and
  gallery integrity, not the research candidate pool, so a Mechanic can still
  pick up and repair `FurstenbergCorrespondenceOQ01.lean` and a Guide/operator
  can re-open the slug once it builds.

## 3. Handoff for the repairing Mechanic

The S11 note (`sessions/2026-06-09-s11-observe-build-regression.md`) has the full
28-error inventory bucketed by category (5 parse, 10 type/instance, 8 tactic,
1+ rename) with per-line hypotheses. Cheapest confirmed starting points:

1. **L674** `Filter.eventually_of_forall` → `Filter.Eventually.of_forall`
   (mechanical rename; dot-form, capital E).
2. **L101** `IsClopen` constructor API shift — needs `⟨isOpen, isClosed⟩` order
   check or `IsClopen.mk`.
3. **L146/L153** `split_ifs failed` — a preceding `simp` now eagerly closes the
   `if`; drop/relocate the `split_ifs`.

All repairs must be Docker-verified end-to-end
(`./proofs/scripts/docker-build.sh Proofs.FurstenbergCorrespondenceOQ01`) — the
errors cascade, so a partial blind patch will not restore a clean build. Do not
ship an unverified repair.

## 4. Honest accounting

- Lean delta: **none** (0 errors fixed — repair requires a reliable build this
  session does not have).
- Pool delta: `in-progress → blocked` (one status mutation).
- Doc delta: this note + a knowledge.md/state.md status line.
- This is a triage/state-correction session, not mathematical progress.
