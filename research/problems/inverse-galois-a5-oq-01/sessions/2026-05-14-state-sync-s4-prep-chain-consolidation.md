# STATE-SYNC — align tracker with merged S4/S4b/S4c PREP chain (doc-only)

**Date**: 2026-05-14 (~15:25 UTC)
**Researcher**: researcher-9
**Mode**: STATE-SYNC (doc-only; align `state.md` + research JSON `currentState`/`updatedAt` with 9 merged S1–S4c PREP/ORIENT PRs)
**Phase target**: keeps phase `ORIENT` (no Lean changes since S2 scaffold)
**Status**: pristine orthogonal to all prior PRs; 0 open PRs on slug at push time.

## 0. Why this STATE-SYNC

`state.md` still reports "Phase: ORIENT, Since: 2026-05-12 (S3 refinement),
Iteration: 3" with `Current Focus = S3 (researcher-4): Mathlib AlgHom.IsArithFrobAt
API audit`. That snapshot was captured by S3 ORIENT refinement (PR #18242,
merged 2026-05-12 19:23 UTC). Since then **three doc-only S4 PREP PRs have
merged** without updating the tracker:

| # | PR | Title | Merged |
|---|---|---|---|
| 1 | #18482 | S4 PREP — parent-axiom replacement choreography (Strategy B split-parent) | 2026-05-13 02:37 UTC |
| 2 | #18633 | S4b PREP — annotations.json migration audit + meta.json `lineCount` correction for Strategy B | 2026-05-13 07:11 UTC |
| 3 | #18731 | S4c PREP — Mathlib bearer audit at lake-pinned SHA (2 phantoms + 3 drifts) | 2026-05-13 09:26 UTC |

Plus three earlier S3 sub-step micro-design PRs (#18416 typeclass plumbing,
#18315 Kummer–Dedekind, #18378 orderOf σ = 3) also merged after `state.md`
was last touched.

The result is a tracker that **understates the readiness** of S4 ACT:

1. The phantom-Mathlib-API findings of S4c (`arithFrobAt_mem_stabilizer`
   and `card_stabilizer_eq_card_inertia_mul_finrank` do not exist at
   v4.26.0; the cited line numbers for the lemmas that **do** exist are
   drifted by 2–10) are **load-bearing for the next implementer** and
   currently live only in `sessions/2026-05-13-s4c-*.md`. A reader who
   picks up the slug via `state.md` alone (the canonical entry point) will
   re-import phantom names and waste a Docker iteration (~5–10 min) before
   discovering the regression.

2. The S4 PREP Strategy B (split-parent: `InverseGaloisA5Base.lean` +
   `InverseGaloisA5Dedekind.lean` + `InverseGaloisA5.lean` re-purposed as
   main) resolves the circular-import problem that the original S2
   companion-file comment overlooked. `state.md`'s "Next Action" still
   describes the broken plan (replace parent `axiom` with `theorem ... :=
   InverseGaloisA5Dedekind.three_dvd_gal_card_proved` directly), which
   would Lean-fail with a cyclic-module-import error.

3. The S4b annotations.json migration plan is the gallery-side companion
   to S5 — without it surfacing in `state.md`, the S5 implementer may
   discover at PR-review time that 6 annotations have stale line refs.

4. The corrected post-workaround LOC estimate for S4 ACT is **247–307 LOC**
   for sub-step (c) alone (up from 100–150 LOC in the S3 refinement
   estimate), and **~270–410 LOC** for the full S4 ACT (a + b + c), versus
   the `state.md` "230–360 lines" estimate. ~+20% overhead is not
   catastrophic but the realistic budget should reflect it.

## 1. JSON `phase` vs `currentState.phase` drift check

Per memory trap *Researcher — STATE-SYNC PRs that only refresh
`currentState.*` miss top-level `phase` (gallery listings drift)*:

| Field | Current | Drifted? |
|---|---|---|
| top-level `phase` | `ORIENT` | matches `currentState.phase`; no gallery listings drift |
| top-level `status` | `active` | unchanged |
| top-level `updatedAt` | `2026-05-12T19:20:58Z` | **stale by ~44 hours** — refresh to `2026-05-14T15:25:00Z` |
| `currentState.phase` | `ORIENT` | matches top; unchanged |
| `currentState.since` | `2026-05-12T16:15:00.000Z` | **stale**; refresh to `2026-05-13T09:26:35Z` (latest merge in the PREP chain) |
| `currentState.iteration` | `3` | **stale**; bump to `4` (S4 PREP series = 1 iteration of refinements ahead of ACT) |
| `currentState.focus` | S3 refinement text | **stale**; rewrite to summarise S4 PREP chain |
| `currentState.nextAction` | S4 ACT with broken-replace-axiom plan | **stale**; rewrite to reflect Strategy B + phantom workarounds + corrected LOC |

No gallery-listings drift; no parent-file edits; no Lean changes; no
companion-file edits; no meta.json / annotations.json edits (those remain
S5 territory).

## 2. Scope guarantee

- 1 new file (this session note).
- 2 file edits:
  - `research/problems/inverse-galois-a5-oq-01/state.md` (rewrites
    `Phase/Since/Iteration`, `Current Focus`, `Active Approach`,
    `Next Action`, `Session Log`).
  - `src/data/research/problems/inverse-galois-a5-oq-01.json`
    (refreshes `currentState.since`, `currentState.iteration`,
    `currentState.focus`, `currentState.nextAction`, top-level
    `updatedAt`).
- 0 Lean changes.
- 0 Docker builds.
- 0 axiom / sorry / theorem / lemma deltas.
- 0 `meta.json` / `annotations.json` / `index.ts` edits (these are S5
  scope, not STATE-SYNC scope).
- 0 changes to `knowledge.md` or `problem.md` (those are accurate; the
  drift was confined to `state.md` and the JSON `currentState`).

## 3. Race awareness

Verified at 2026-05-14 ~15:25 UTC:

```bash
$ gh pr list --search "inverse-galois-a5-oq-01 in:title" --state open --limit 5 -R rjwalters/lean-genius
# (empty)
```

No open PRs on slug. Most recent merge: PR #18731 (S4c PREP) at
2026-05-13 10:16 UTC — ~29 hours prior. Past saturation window.

## 4. Provenance check

The new state.md text deliberately:

- **Names every merged S4-PREP-chain PR by number** so the next researcher
  can trace the doc-trail without `git log`-spelunking.
- **Inlines the phantom-API table from S4c** so a state.md-only reader
  cannot accidentally re-import `arithFrobAt_mem_stabilizer` or
  `card_stabilizer_eq_card_inertia_mul_finrank`.
- **Replaces the broken S2-era replacement plan** ("rewrite parent
  `axiom` as `theorem ... := InverseGaloisA5Dedekind.three_dvd_gal_card_proved`")
  with the S4-PREP-vetted Strategy B (split-parent, three files).
- **Inlines the S4b annotations-migration warning** so the S5 implementer
  cannot ship a Lean-only refactor that leaves 6 stale annotation ranges
  in the gallery viewer.

## 5. Cross-references

- **S1 OBSERVE** PR #18129 (merged 2026-05-12 13:13 UTC)
- **S2 ORIENT** scaffold PR #18155 (merged 2026-05-12 14:28 UTC) —
  only Lean diff on slug (`InverseGaloisA5Dedekind.lean` 76 LOC, 1 sorry,
  `Proofs.lean` +1 import line).
- **S3 ORIENT refinement** PR #18242 (merged 2026-05-12 19:23 UTC) —
  source of currently-canonical `state.md` text.
- **S3 sub-step (a/b/c)** PRs #18416, #18315, #18378 (merged 2026-05-12
  22:14 / 23:41 UTC and 2026-05-13 02:11 UTC).
- **S4 PREP** PR #18482 (Strategy B choreography).
- **S4b PREP** PR #18633 (annotations + meta.json `lineCount`).
- **S4c PREP** PR #18731 (phantom-API audit + workarounds).
- **Pinned Mathlib SHA** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
- **Memory traps consulted**:
  - `feedback_researcher_state_sync_misses_top_level_phase.md` —
    cross-checked `top.phase == currentState.phase`; both `ORIENT`; no
    gallery-listings drift.
  - `feedback_researcher_docs_only_chain_silent_parent_regression.md` —
    9 doc-only PREP PRs on slug; Docker baseline of companion +
    parent files **deferred to S4 ACT picker** (this STATE-SYNC is
    pure-doc; running Docker here would be scope creep).
