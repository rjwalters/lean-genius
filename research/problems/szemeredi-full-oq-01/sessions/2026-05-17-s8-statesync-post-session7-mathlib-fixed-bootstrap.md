# Session 8 — S8 STATE-SYNC: absorb Session 7 (PR #14878) + bootstrap sessions/ dir

**Date**: 2026-05-17T00:50:00Z
**Researcher**: researcher-3
**Mode**: STATE-SYNC (doc-only; no Lean, no gallery, no knowledge body, no
build verification)
**Outcome**: CATCHUP — 14-day-stale post-fix-PR drift absorbed into state.md
+ JSON + registry; sessions/ dir bootstrapped.
**Predecessor**: Session 7 (researcher unknown, 2026-05-02, PR #14878 merged
2026-05-02T21:18:35Z, T-14d8h).

## 1. Why S8 fires (strict refinement, doc-only)

Claim-random landed at 2026-05-17T00:47Z (knowledge score 35, RICH MODERATE+
tier, Tier A significance=9). Pre-S8 audit revealed:

- `knowledge.md` carries a full Session 7 epilogue (2026-05-02) reporting
  PROGRESS — 6 Mathlib API drift root errors fixed (cascading to ~35 build
  failures) via PR #14878 (merged 2026-05-02T21:18:35Z).
- `progressSummary` in JSON top-level explicitly says: `"PROGRESS: Session 7
  (2026-05-02) fixed 6 Mathlib API drift root errors causing 35 cascading
  build failures (PR #14878). File should now be buildable. 1 sorry remains:
  limit_invariant_on_cylinder ..."`.
- BUT `state.md` head + JSON `currentState.{phase, focus, nextAction,
  iteration, blockers, attemptCounts}` + `lastUpdate` + registry `phase` /
  `lastUpdate` ALL still stamped pre-Session-7 (`Phase: BLOCKED`,
  `Iteration: 4`, `lastUpdate: 2026-04-27T22:30Z`).
- Pool entry status was `available` pre-claim — set by an unidentified
  operator between 2026-04-27 (when Session 6 explicitly moved it to
  blocked) and 2026-05-17 (now), without state.md / JSON sync.

The 14-day drift mis-signals to the pool / claim-rotation / Judge / Auditor
that the slug remains in its pre-fix BLOCKED state. The re-claim cycle
that Session 6 wanted to stop has clearly resumed (I'm proof of it: I
just claim-randomed here).

## 2. Pre-S8 drift inventory (9 items)

| # | Surface | Pre-S8 | S8 fix | Severity |
|---|---|---|---|---|
| 1 | `state.md` Phase | `BLOCKED` | `ACT` | HIGH |
| 2 | `state.md` Iteration | `4 (last update: 2026-04-27 Session 6)` | `8 (incl. S8)` | HIGH |
| 3 | `state.md` Current Focus | `BLOCKED on Mathlib API drift ... 35 errors` | post-fix narrative | HIGH |
| 4 | `state.md` Active Approach | `None. File cannot build` | `limit_invariant_on_cylinder` proof activation | HIGH |
| 5 | `state.md` Blockers | `35 Mathlib API drift errors` | discharged via PR #14878 (HOST blockers remain) | HIGH |
| 6 | `state.md` Next Action | `Operator must upgrade Mathlib pin and repair 35 errors` | S9 ACT — host recovery + paste limit_invariant proof | HIGH |
| 7 | JSON `currentState.phase` | `BLOCKED` | `ACT` | HIGH |
| 8 | JSON `currentState.{focus, nextAction, iteration, blockers, attemptCounts}` | pre-Session-7 | Session-7-aware | HIGH |
| 9 | JSON `lastUpdate` + `registry.json` `phase` / `lastUpdate` | 2026-04-27 / OBSERVE / 2026-04-24 | 2026-05-17 / ACT / 2026-05-17 | MED |
| (bonus) | `sessions/` dir | ABSENT (canonical 4th planning artifact gap) | bootstrap with this S8 memo | LOW |

S8 closes all 10 in a thin 4-file doc-only motion.

## 3. Session 7 details (canonical, from knowledge.md)

Session 7 (2026-05-02, REVISIT mode, MODERATE knowledge tier 32) fixed 6
root API drift errors:

| # | Lemma / theorem | Error category | Fix |
|---|---|---|---|
| 1 | `shift_iterate` (zero case) | `simp [Function.iterate_zero]` failed | `rfl` |
| 2 | `shift_iterate` (succ case) | weak ih without `generalizing k`; `ring_nf` left unsolved goals | `induction n generalizing k`, `simp only [... comp_apply]`, `congr 1; omega` |
| 3 | `cylinder_isClopen` | `isOpen_eq_of_isOpen_singleton` removed from Mathlib | `(isOpen_discrete {b}).preimage (continuous_apply i)` |
| 4 | `shift_indicator_zero`, `indicator_mem_cylinder`, `orbit_indicator_hits` | `split <;> simp_all` failed (simp partially reduces if-then-else) | `split_ifs with h <;> simp [h]` |
| 5 | `CompactSpace Bool` | `Finite.instCompactSpace` removed | `inferInstance` |
| 6 | `filter_shift_card_le` | `split` fragile on if-then-else | `split_ifs` |

Session 7 also flagged 1 **mathematical bug** (not just API drift): the
`shift_iterate` succ case was mis-stated without `generalizing k`. This is
a real correctness improvement, not a workaround.

PR #14878 merged 2026-05-02T21:18:35Z, T-14d8h before S8.

## 4. Post-S8 state (what S9 inherits)

**Build status**: presumed buildable per Session 7's assertion + the merged
PR #14878. NOT Docker-verified in S8 (Docker `info` hangs in 5 s; host-cron
territory). S9 ACT should re-verify build before pasting limit_invariant.

**Remaining work** (per knowledge.md Session 7 Next Steps):

1. `limit_invariant_on_cylinder` at line 779 of
   `proofs/Proofs/FurstenbergCorrespondenceOQ01.lean`. The 60-line proof
   structure is documented in the file comment at line ~760. Uses ENNReal
   Portmanteau → Measure equality and the Cesàro infrastructure from
   Session 2.
2. `seqCompact_probabilityMeasure_cantor` (~150-200 lines via Prokhorov
   ingredients in Mathlib v4.26). Order: S9 ACT then S10 ACT, in that
   sequence (Session 7 ordered).

**Real sorry count**: 1 (line 779). Two other `sorry` text matches in the
file are inside docstring comments (`"Remaining sorry (1):"` line 878 and
`"One sorry for T-invariance limit algebra"` line 923).

**Axioms**: pin-stable per Session 7 (no axiom delta from PR #14878).

## 5. Host gate snapshot (2026-05-17T00:47Z)

```
$ date -u +%Y-%m-%dT%H:%M:%SZ
2026-05-17T00:50:00Z

$ df -h / | tail -1
/dev/disk3s1s1   926Gi    16Gi   3.4Gi    83%    458k   35M    1%   /

$ timeout 5 docker info 2>&1 | head -5   # Client only, no Server: section
Client:
 Version:    29.4.1
[Server: section absent — daemon hung]

$ ls -la proofs/.lake | head -1
lrwxr-xr-x  proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake
(symlink off-worktree to main repo — NOT a self-cycle; usable when
 host disk + Docker recover)
```

Host gate is RED on disk + Docker. These are the same REDs blocking the
adjacent `descartes-rule-of-signs-oq-02-oq-01-oq-02` slug's S3 ACT (see
S3 STATE-SYNC PR #19965 of same researcher-3 session). Host-cron territory.

## 6. Trap inventory (memory citations consulted)

- `_long_completed_slug_with_recent_observe_audit_..._materially_contradicts_observe_findings` — N/A, this slug is ACT not COMPLETED.
- `_claim_random_lands_on_long_completed_slug_due_to_research_json_stale_while_statemd_gallery_lean_all_canonical_inverse_of_statemd_drift_pattern` — N/A, here the STATE-SYNC direction is INVERTED: state.md + JSON are STALE; knowledge.md is canonical.
- `_state_md_three_sessions_behind_sessions_dir_with_mechanic_cascade_already_discharging_blockers` — partial match (state.md is N sessions behind); but here no mechanic cascade exists; the discharging entity is a single Session-7 PR #14878 followed by an unidentified pool-status update.
- `_postship_pivot_to_long_completed_slug_with_statemd_phase_drift_..._bootstrap_sessions_dir` — match in spirit (3-file doc-only + sessions/ bootstrap pattern) but slug is ACT not COMPLETED.

The closest-matching pattern is:
- "ACT-phase slug with single-PR-fixed predecessor (Session 7 / PR #14878,
  T-14d) + state.md/JSON drift not absorbed + sessions/ dir absent +
  knowledge.md is canonical, ship 4-file doc-only STATE-SYNC."

This pattern is sufficiently distinct from existing memory entries that it
may warrant a new memory once shipped — but only if the pattern recurs
across slugs (single recent fix-PR + drift + sessions/ absent).

## 7. Honesty calibration

- This PR ships **0 build verification**. Session 7's "file should now be
  buildable" assertion is taken at face value; S8 cannot run Docker.
- This PR ships **0 mathematical advance**. The 1 remaining sorry at line
  779 (`limit_invariant_on_cylinder`) is unchanged; ergodic-theoretic
  Szemerédi proof is no closer to discharged.
- This PR ships **8 narrative drift fixes** (state.md HEAD, 7 JSON
  field edits) + **2 registry edits** (phase + lastUpdate) + **1 sessions/**
  dir bootstrap.
- This PR ships **0 pool status change**. Per Session 7 step 4 the intended
  transition is "→ available once build confirmed". S8 cannot confirm the
  build (no Docker). Pool will be `in-progress` post-claim → operationally
  released via `claim-problem.sh release` at end of session, returning to
  whatever the pool currently records (was `available` at claim time).
- Total: 4-file doc-only PR. No mathematics, no Lean, no build verification,
  no axiom delta, no sorry delta.

The PR is honest about its narrowness. It is a 14-day catchup of stale
narrative surfaces, not a research advance.

## 8. Picker decision matrix (next researcher landing on this slug)

| Disk state | Docker state | Build status | Recommended action | Phase |
|-----------|--------------|--------------|---------------------|-------|
| ≥ 30 Gi avail | responsive < 5 s | clean | **S9 ACT** — paste `limit_invariant_on_cylinder` proof at line 779 (structure in file comment line ~760) | ACT |
| ≥ 30 Gi avail | responsive < 5 s | breaks | **S9 DOCTOR** — diagnose new drift (Mathlib pin advanced? File touched by sibling PR?); fix; ship | ACT (drift-repair) |
| ≥ 30 Gi avail | hung | unknown | **release** — wait for Docker recovery; cannot Lean-edit confidently without build cycle | release |
| < 30 Gi avail | either | unknown | **release** OR thin S{N}-STATE-SYNC only if new HIGH drift accumulates (Session-9+ happens, drift recurs, etc.) | STATE-SYNC or release |

Current state (T = 2026-05-17T00:50Z): disk 3.4 Gi < 30 Gi, Docker hung →
S8 STATE-SYNC fires (this PR) because of the 14-day post-Session-7 drift
HIGH severity. Next landing should re-evaluate against this matrix.

## 9. References

- **PR #14878** — Session 7 Mathlib API drift repair, merged
  2026-05-02T21:18:35Z, T-14d8h.
- `knowledge.md` Session 7 (2026-05-02) — canonical record of the 6 fixes.
- `knowledge.md` `progressSummary` — already says "PROGRESS: Session 7
  ... PR #14878"; S8 absorbs the rest of the surfaces.
- `state.md` (this slug, post-S8) — Phase BLOCKED → ACT, S8 block prepended.
- `src/data/research/problems/szemeredi-full-oq-01.json` — 7-field edit.
- `research/registry.json` — phase OBSERVE → ACT.
- `proofs/Proofs/FurstenbergCorrespondenceOQ01.lean` — line 779 holds the
  1 remaining sorry; line ~760 documents the 60-line proof structure.
- Memory: `_postship_pivot_to_long_completed_slug_with_statemd_phase_drift_..._bootstrap_sessions_dir` (closest pattern; slug is ACT here, not COMPLETED).
- Sibling researcher-3 session: descartes-rule-of-signs-oq-02-oq-01-oq-02
  S3 STATE-SYNC (PR #19965) — same host gate REDs, similar STATE-SYNC
  catchup pattern.
