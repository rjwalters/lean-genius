# S7 STATE-SYNC tick 2026-06-04 — companion registration absorption

**Researcher**: researcher-1 (claim `researcher-56176`, this cycle)
**Mode**: STATE-SYNC tick — doc-only
**Phase**: RESEARCH-COMPLETE (unchanged since S5, 2026-05-16T15:40Z)
**Elapsed since S6**: 3 days (S6 = 2026-06-01)

## Why this tick

Slug is RESEARCH-COMPLETE since S5 (2026-05-16). The state.md
explicitly contemplated this exact motion for a future researcher
claim:

> If a future researcher claims this slug, the appropriate motion
> would be either a thin STATE-SYNC absorbing eventual mechanic
> Docker-verify + sibling PRs into the slug's narrative, or writing
> one of the upstream Mathlib contribution candidates (which would
> be Mathlib-PR work, not slug-work).

S7 chooses the first option: a thin STATE-SYNC absorbing one
materially relevant mechanic event from the past 3 days.

## Material event since S6

**Mechanic PR #21965** — `fix(meta): greens-theorem-oq-01-oq-01-oq-02
register OQ01/OQ02 orphan companions` — merged 2026-06-02T07:24:57Z.

Scope: 1 file changed, +5/-1 lines, in
`src/data/proofs/greens-theorem-oq-01-oq-01-oq-02/meta.json` only.

The `leanFile.additionalFiles` field was added:

```json
"additionalFiles": [
  "Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean",
  "Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean"
]
```

This is the gallery-integration counterpart to S1 OBSERVE's design
disposition: this OQ-only slug never warranted its own
`src/data/proofs/<slug>/` directory; instead its Lean file lives as
a companion of the parent gallery entry `greens-theorem-oq-01-oq-01-oq-02`.
The mechanic registration makes that companion relationship explicit
and stops the auditor's orphan scan from flagging it.

This is the third gallery-integration loose end discharged by the
mechanic cycle for this slug, after:

- PR #19218 (parent file repair) — independently validated the
  bridge pattern at this slug's line 101-102.
- PR #19130 (cross-family barrel-split imports) — cleared the
  IntervalIntegral import drift cascade.

The fourth (Docker-verify of this slug's own 104-LOC file) remains
Mechanic/Auditor scope and was not invoked since S6.

## Negative confirmations

Each re-checked at S7 entry:

| Surface | Result |
|---|---|
| `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean` last touched | S3 ACT (#18944, 2026-05-13) — no later commits |
| Slug-file line/theorem/axiom/sorry counts | 104 / 1 / 0 / 0 — unchanged since S3 ACT |
| Sibling `OQ02OQ03` Bochner discharge | not yet shipped — sibling-slug scope; forward-pending |
| Mathlib pin | `2df2f0150c…` (v4.26.0) — stable ~23 days |
| Chain-build drift events since #21782 | none |
| Researcher-side blockers | none material this cycle (no Docker call attempted) |

The earlier S6 `blockers[]` entry referencing "Docker daemon hung +
host disk 100%" was a researcher-side condition specific to that
cycle's claim and is not a slug-level blocker. S7 clears the
`blockers[]` array in the JSON accordingly (the Mechanic/Auditor
path for Docker-verify is unaffected by researcher-side disk
pressure).

## Ship scope

3 files:

1. `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/state.md`
   — prepend S7 block above S6, refresh head metadata. S6 + earlier
   narrative preserved verbatim below the new block.
2. `src/data/research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02.json`
   — iteration 9 → 10, `lastUpdate` → 2026-06-04T18:00Z,
   `currentState.focus` rewritten to describe S7, `blockers[]`
   cleared (was a researcher-side cycle artifact), `nextAction`
   refreshed (substance unchanged from S6).
3. `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/sessions/2026-06-04-s7-state-sync-companion-registration.md`
   — this memo.

## NOT touched

- Lean files (no semantic change since S3 ACT)
- `knowledge.md` (S5's Mathlib upstream contribution catalog and
  research-complete posture remain accurate; nothing in #21965
  invalidates that content)
- Parent slug's `meta.json` (mechanic PR #21965 already did the
  authoritative update)
- Sibling slug state/JSON files
- `leanFiles[]` numeric audit (no slug-file LOC drift; the parent's
  registered `additionalFiles` is parent-slug metadata, not slug
  research-state metadata)
- Mathlib pin walks

## Iteration accounting

- Iteration 9 → 10 (S7 STATE-SYNC tick).
- `attemptCounts.total` 9 → 10.
- `attemptCounts.currentApproach` 7 → 8 (still the wrapper /
  alternative-interface approach; no new approach).
- `attemptCounts.approachesTried` unchanged at 1.

## Forward items at S7 (unchanged from S6)

1. **Docker-verify** of this slug's 104-LOC file —
   `./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ02`.
   Mechanic/Auditor scope. Expected routine: parent's same bridge
   pattern compiled cleanly in #19218 (3058/3058 jobs); chain-build
   drift from v4.26.0 cleared by #21782 and #19130.
2. **Sibling OQ02OQ03 Bochner discharge** — sibling-slug scope.
   Likely 1-LOC patch following parent #19218 pattern.
3. **Mathlib upstream contributions** — `knowledge.md` §"S5 Mathlib
   contribution candidates": 3 numbered candidates
   (`Measure.restrict_prod_restrict` wrapper, low/medium upstream
   value; `LocallyIntegrable.integrableOn_of_isCompact` variant,
   low upstream value; `Measure.restrict_pi_restrict` arbitrary-index
   generalization, higher upstream value). Out-of-band mathlib4 PR
   scope; any contributor.

## When (if ever) to ship S8

S8 would be appropriate when:

- Docker-verify of this slug's file completes (would absorb the
  cleared `(build pending)` flag in `knowledge.builtItems[]`); or
- Sibling OQ02OQ03 Bochner discharge ships (would absorb the
  cross-family closure into the slug's narrative); or
- A second material gallery-integration event occurs (e.g., an
  auditor decision to promote the OQ-only slug into a standalone
  gallery entry).

Absent any of the above, the slug should not be re-claimed for
further STATE-SYNC ticks; the JSON status should be allowed to
drift toward the slug-pool's `RESEARCH-COMPLETE` terminal state.
