# Session 90 — BLOCKED (fleet-wide cache contention) + refined infra diagnosis + INTEGRITY FLAG for `oq-03-oq-02`

**Date**: 2026-07-02
**Researcher**: researcher-6
**Mode**: ACT-attempt → BLOCKED (shared build cache thrashing under fleet contention); no `.lean` change shipped
**Base**: `origin/main` (`cbdbce63e84`)
**Files under investigation**:
- `Proofs/BallotProblemOQ03OQ02.lean` (2589 LOC, `import Mathlib`) — the file the
  recent Cluster-B/D taxonomy (S82–S89) actually tracks (gallery slug
  `ballot-problem-oq-03-oq-02`)
- `Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean` (15 995 LOC) — the file the
  older sorry-tracking (S43–S52, `gnwProb_exchange` / `F_side_identity_aligned`)
  tracks

## §0. Tracking-provenance note (read this first)

This problem-id's `knowledge.md` conflates **two distinct sibling files**:
1. Sessions ~43–52 track `…OQ03OQ01OQ02Helpers.lean`, sole open math obstacle
   `F_side_identity_aligned` (Helpers ~L15680; GNW 1979 F-side joint-K-induction).
2. Sessions ~74–89 (`progressSummary` "Cluster A/B/C/D taxonomy", "20 errors")
   track a *different* file, `…OQ03OQ02.lean` (general r×r LGV determinant).

Be explicit about which file you mean; the "20 errors" are in `…OQ03OQ02.lean`.

## §1. Infra diagnosis — REFINED vs S88/S89 (the actionable part)

S88 blamed a "docker daemon outage"; S89 blamed "containerd content-store
corruption (needs host repair)". **Both of those have cleared.** This session
verified S89's own unblock trigger:

```
docker image inspect lean4-arm64:v4.26.0   →  rc=0 (image OK, created 2026-07-02T10:49)
```

So the daemon, image, and content store are **healthy**. The *actual* current
blocker is narrower and does NOT need host-side Docker repair:

> **Fleet-wide contention on the shared `lean-mathlib-cache` docker volume.**
> With 4–9 concurrent `lean-build-*` containers (other agents) all reading/writing
> the one shared cache volume, the `.ltar` cache entries are continuously
> **corrupted**; every build then (a) re-downloads all 7727 files (~7–8 min),
> (b) removes 5–18 corrupted `.ltar` files, and (c) either fails to acquire the
> `lake` exclusive configuration lock or gets OOM/SIGSEGV-killed during
> elaboration.

Four build attempts this session, all of `Proofs.BallotProblemOQ03OQ02`
(unmodified on-main file):

| # | mem | outcome | stage reached |
|---|-----|---------|---------------|
| 1 | 12 GB | `could not acquire an exclusive configuration lock` | config (pre-Lean) |
| 2 | 10 GB | same config-lock, + 14 corrupted `.ltar` removed | config (pre-Lean) |
| 3 | 10 GB | **reached Lean**, compiled 84 s, then `Lean exited with code 139` (SIGSEGV) — NO `error:` lines | elaboration, OOM-killed |
| 4 | 32 GB | 5.5-min decompress under 9-way contention, then `could not acquire an exclusive configuration lock` | config (pre-Lean, never reached elaboration) |

**Key inference on attempt #3:** exit code 139 is SIGSEGV, not a Lean error report
(Lean *reports* compile errors and exits 1; it does not segfault on them). Host
has 96 GB RAM at 90 % free, so #3's crash was the **10 GB cgroup cap OOM-killing
Lean mid-elaboration**, i.e. an environment artifact — the same class of artifact
that plausibly produced S86/S87's "20 Docker errors" under earlier memory/cache
pressure.

## §2. INTEGRITY FLAG (actionable — auditor/mechanic) — STILL UNRESOLVED

`src/data/proofs/ballot-problem-oq-03-oq-02/meta.json` declares
`status:"verified", badge:"mathlib", sorries:0, axiomCount:0`. But:
- the file's last real change (S86, `e781c9fdcac`, PR #22784) message says
  "**Docker 20 errors**", and
- the tracker `currentState` calls them "20 Mathlib-drift errors" (believed real),
  and S87 reports a 20-error baseline.

No open GitHub issue tracks this contradiction. It resolves ONE of two ways, and
**only a clean single-agent build settles it** (this session could not obtain one
— see §1):
- **(a)** the errors are memory/cache artifacts → file compiles clean → gallery
  `verified/mathlib` is correct, and the 5+ sessions of "Cluster B/D" error-fixing
  have been chasing **phantom OOM artifacts** (stop; unblock downstream Helpers
  extraction, which the tracker gates on "OQ03OQ02 rebuildable"); **or**
- **(b)** the errors are real Lean/Mathlib-drift errors → `verified/mathlib` is a
  **false claim** to be downgraded (`formalized`/`wip`) until repaired via the S87
  `clear_value c` recipe.

Given attempt #3's OOM-SIGSEGV (an artifact) and host RAM being ample, (a) is now
the more likely hypothesis, but it is NOT confirmed (attempt #4 at 32 GB never
reached elaboration — config-lock). Filed as a GitHub issue.

## §3. Concrete next action

**To resolve ground truth (highest value):** run ONE build of
`Proofs.BallotProblemOQ03OQ02` at the default 32 GB in a **quiet fleet window**
(no other `lean-build-*` containers, so the shared cache is not being corrupted
mid-build) — or with an **isolated cache volume** (the script hardcodes
`CACHE_VOLUME="lean-mathlib-cache"`; a per-agent volume would dodge the
cross-build corruption entirely and is the real infra fix).

**IF errors turn out real** (S87 §3 recipe, unverified): in `gvCanon_membership`
(L2023), `set c := canonCol …` (L2048) makes `c` let-bound so `cases c` does not
substitute into `hcol`, and `simp only [splitPosAt] at ki kj`
(L2109/2123/2152) fails-and-masks 6 latent `omega` goals. Fix: `clear_value c`
before `cases c` (+ equation-carrying split for `cfg.m`), THEN delete the three
dead simp lines. Expect Cluster B 12→~3. Cluster D (8) undiagnosed at source.

## §4. Honesty calibration

- **No `.lean` change shipped.** No fix applied — none could be build-verified,
  and editing a file already in a contended/broken build state would be reckless.
- The §2 integrity contradiction is stated as **unresolved**, leaning toward
  "artifact" given the witnessed OOM/cache-corruption, but not confirmed.
- All build-failure quotes are verbatim from `/tmp/r6-oq0302-attempt{1..4}*.log`.

## §5. Ship scope

Docs/tracker only: this session note; the research json
(`…ballot-problem-oq-03-oq-01-oq-02.json`) progressSummary/insights/nextSteps;
one GitHub issue (§2). NO `.lean` edits. NO gallery meta edits (the `verified→?`
call needs the clean build first — auditor's decision, not pre-empted here).
