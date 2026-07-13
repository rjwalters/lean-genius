# S4 STATE-SYNC — long-completed slug + research-JSON / state.md / pool drift catchup (doc-only)

**Slug**: erdos-1071
**Phase**: ACT (per per-slug research JSON, stale) → COMPLETED (matches `research/registry.json` already-true since 2026-03-24)
**Iteration**: 3 → 4
**Date**: 2026-05-17
**Researcher**: researcher-10
**Predecessor (state.md)**: original boilerplate, never updated past initial scaffold (`Phase: NEW, Iteration: 1`, 2026-01-15)
**Predecessor (Lean file)**: PR #10880 by rjwalters (`Erdős #1071: add Zorn existence proof + Danzer axiom (0 sorries, 1 axiom)`), merged 2026-04-21T11:07Z (T−26d)
**Predecessor (registry graduation)**: 2026-03-24T17:16:51Z (T−54d, via `research/registry.json` `phase: COMPLETED, status: graduated`)
**Predecessor (other touches)**: PR #17495 by mechanic 2026-05-08T22:54Z (T−9d, batch `definitionCount` sync over 17 entries incl this slug — but only touched gallery `meta.json`, not the research JSON registry).

---

## §0. TL;DR

The slug `erdos-1071` has been *registry-COMPLETED* since 2026-03-24 (~54
days ago). Three Lean-bearing PRs (`#6190` early theorems + optimal constants,
`#6993` geometric foundations 10 thm, `#7633` and `#10880` Zorn existence
proof + Danzer axiom) plus one mechanic batch sync (`#17495`) closed out the
gallery side. The per-slug **research JSON registry**
(`src/data/research/problems/erdos-1071.json`), the **per-slug
`state.md`**, and the **candidate pool** retained pre-completion fields:

- Top-level `phase: ACT`, `status: active` (vs registry `COMPLETED` /
  `graduated`).
- `currentState.phase: ACT`, `currentState.iteration: 3`,
  `currentState.focus: "Proved structural geometry lemmas. 3 deep axioms
  remain."` (pre-#10880 framing — Zorn / Danzer split eliminated all but
  one axiom, the file now stands at 1 axiom, not 3),
  `currentState.nextAction: "Begin problem exploration."` (boilerplate),
  `currentState.attemptCounts.total: 0`.
- `lastUpdate: 2026-03-28T23:10:00Z` (pre-#10880).
- `leanFiles[0].lineCount: 324` (off-by-one vs canonical `wc -l = 323`;
  legacy `split('\n').length` convention from a pre-mechanic-canonicalization
  `pnpm build` regeneration).
- `leanFiles[0].theoremCount: 22` (narrow `^theorem `/`^lemma ` convention,
  missing the line-244 `private lemma packing_chain_union`. Canonical
  mechanic-batch raw regex `^(protected |private |noncomputable )*(theorem|lemma) `
  = 23, which matches the gallery `meta.json.meta.theoremCount = 23`).
- `state.md`: still the *initial scaffold* (`Phase: NEW, Iteration: 1`).
- `sessions/` directory: absent.
- Candidate pool entry: `status: in-progress` (claim-random offered the
  slug to researcher-10 at 2026-05-17T05:23Z under the `in-progress` flag,
  which is what surfaced the drift).

**S4 scope**: doc-only, 3 files (`state.md` full rewrite, surgical research
JSON edits, NEW sessions memo), 0 Lean changes, 0 gallery `meta.json`
edits, 0 sibling-slug edits, 0 new theorems / axioms / sorries. Erdős-1071's
`Erdos1071Problem.lean` remains **323 LOC, 23 thm, 14 def, 1 axiom, 0
sorry**. After PR merge: `claim-problem.sh update erdos-1071 completed`
flips pool `in-progress → completed`.

---

## §1. Why S4 fires

**Trigger**: claim-random landed researcher-10 on erdos-1071 at
2026-05-17T05:23:03Z (90-min TTL, knowledge score 33 = RICH). Recency
probe (`gh pr list --search erdos-1071 --state all`):

- Last PR touching the slug: #17495 (mechanic batch, 2026-05-08, T−9d) —
  gallery `meta.json` only, not the research JSON registry.
- Last *substantive* PR: #10880 (Apr 21, T−26d) — Zorn + Danzer axiom.
- 0 open PRs touching this slug, 0 ≤T-2h merges anywhere on this slug.
- No collision risk; no recent STATE-SYNC predecessor on this slug.

Per the
`_first_claim_lands_on_long_completed_slug_w_T_18d_predecessor_split_undocumented_audit_plus_non_researcher_lean_pr_that_touched_lean_plus_gallery_but_not_research_json_registry_ship_doc_only_S{N+1}_state_sync_plus_post_merge_pool_flip`
memory: claim-random landed on a long-completed slug whose predecessor was
a non-researcher Lean PR that did not touch the research JSON, leaving
many drift surfaces. Ship doc-only S{N+1} STATE-SYNC + post-merge pool
flip. This case is the same template: predecessor #10880 (`rjwalters`,
not a researcher slot) touched Lean + gallery `meta.json` but not the
research JSON registry, leaving 11 drift surfaces (§2).

The `_postship_pivot_to_active_slug_with_very_recent_statesync_predecessor_release_without_pr_when_residual_drift_below_threshold`
memory does **not** apply: the predecessor is T−26d, not T−6h; residual
drift is 11 surfaces, well above threshold; and "release without PR" is
for cases where another agent's STATE-SYNC already closed the residual
gap. Here no agent has closed any of the registry-side gap since
graduation. Ship.

---

## §2. Drift inventory (research JSON registry vs sources of truth, as of 2026-05-17T05:23Z)

Verified via direct file reads in worktree
`/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-10/`.

| # | Field | Pre-S4 | Post-S4 | Source of truth |
|---|-------|--------|---------|-----------------|
| 1 | top-level `phase` | `ACT` | `COMPLETED` | `research/registry.json` (graduated 2026-03-24); gallery `meta.status: axiomatized` (closed-form: 1 axiom, 0 sorry) |
| 2 | top-level `status` | `active` | `completed` | `research/registry.json` `status: graduated` + 336-slug `completed`+`COMPLETED` precedent in registry |
| 3 | `currentState.phase` | `ACT` | `COMPLETED` | Same as #1 |
| 4 | `currentState.since` | `2026-01-15T14:38:41.571Z` | `2026-05-17T05:23:00.000Z` | This S4 entry timestamp |
| 5 | `currentState.iteration` | `3` | `4` | +1 for this STATE-SYNC |
| 6 | `currentState.focus` | "Proved structural geometry lemmas. 3 deep axioms remain." (pre-#10880) | S4 framing (Zorn-existence + Danzer-axiom + Part-(b) open) | PR #10880 + this PR |
| 7 | `currentState.blockers` | `[]` | `["Danzer's $10-prize construction is not in Mathlib; …"]` | State.md S4 Blockers section |
| 8 | `currentState.nextAction` | `"Begin problem exploration."` (boilerplate) | "None — slug COMPLETED. Optional future work: (1) constructive Danzer, (2) Part (b) witnesses, (3) cosmetic refactor." | State.md S4 Next Action |
| 9 | `currentState.attemptCounts.total` | `0` | `4` | 4 Lean-bearing PRs (#6190 / #6993 / #7633 / #10880) + this S4 STATE-SYNC; older convention `0` was placeholder |
| 10 | `currentState.attemptCounts.approachesTried` | `0` | `2` | "Axiomatic skeleton" → "Zorn + Danzer-axiom split" (per state.md) |
| 11 | `knowledge.progressSummary` | "Total: 20 theorems, 3 axioms, 0 sorries." (pre-#10880; the "3 axioms" were `AreDisjoint`, `disjoint_symm`, `EndpointDisjoint` — all eliminated by #10880; current file has exactly 1 axiom = Danzer) | Refreshed: "23 theorems/lemmas, 14 def + 1 structure + 1 abbrev = 16 definitions, 1 axiom, 0 sorries" | Canonical numerics (§3) + #10880 PR contents |
| 12 | `lastUpdate` | `2026-03-28T23:10:00.000Z` | `2026-05-17T05:23:00.000Z` | This PR |
| 13 | `completed` (new field) | absent | `2026-03-24T17:16:51.000Z` | `research/registry.json` `completed` field for this slug |
| 14 | `leanFiles[0].lineCount` | `324` | `323` | `wc -l proofs/Proofs/Erdos1071Problem.lean = 323` + gallery `meta.json.meta.lineCount = 323` |
| 15 | `leanFiles[0].theoremCount` | `22` (narrow `^theorem `/`^lemma `; missed line-244 `private lemma packing_chain_union`) | `23` | Canonical raw regex `^(protected \|private \|noncomputable )*(theorem\|lemma) ` + gallery `meta.json.meta.theoremCount = 23` |
| 16 | `state.md` Phase | `NEW` | `COMPLETED` | Same as #1 |
| 17 | `state.md` Iteration | `1` | `4` | Same as #5 |
| 18 | `state.md` body | initial scaffold (~28 LOC) | full COMPLETED narrative (~70 LOC) | This PR |
| 19 | `sessions/` directory | absent | bootstrapped with this S4 memo | Convention parity with post-S2 slugs |

(builtItems / insights arrays in the research JSON are left as-is — they
are historically-correct snapshots of *early* progress, and rewriting them
to reflect post-#10880 state would be a content audit, not a STATE-SYNC.
Their staleness is documented above and is below the threshold that
triggers re-authoring the array in a single doc-only PR.)

---

## §3. Canonical numerics audit (Erdos1071Problem.lean)

```
proofs/Proofs/Erdos1071Problem.lean
  wc -l                                                              : 323   (CANONICAL)
  grep -cE '^(protected |private |noncomputable )*(theorem|lemma) '  : 23    (CANONICAL — gallery meta.json.meta.theoremCount = 23)
    breakdown:
      ^theorem                                                       : 20
      ^lemma                                                         : 2     (left_endpoint_mem_segment line 99, right_endpoint_mem_segment line 102)
      ^private lemma                                                 : 1     (packing_chain_union line 244)
  grep -cE '^(noncomputable |protected |private )*def '              : 14
  ^structure UnitSegment where                                       : 1     (line 35)
  ^abbrev Region := Set (ℝ × ℝ)                                      : 1     (line 303)
  ^axiom                                                             : 1     (danzer_finite_maximal_packing line 295)
  grep -cE '\bsorry\b'                                               : 0
```

**Gallery convention** (`src/data/proofs/erdos-1071/meta.json.meta`):
- `lineCount: 323` ✓
- `theoremCount: 23` ✓ (canonical raw regex)
- `definitionCount: 16` ✓ (14 def + 1 structure + 1 abbrev — broad "definitions")
- `sorries: 0` ✓
- `axiomCount: 1` ✓
- `status: axiomatized`, `badge: axiom` ✓ (1 Danzer axiom)

**Research-JSON convention** (`src/data/research/problems/erdos-1071.json.leanFiles[0]`):
- `lineCount: 323` ✓ (was 324, fixed)
- `theoremCount: 23` ✓ (was 22, fixed)
- `axiomCount: 1` ✓
- `defCount: 14` ✓ (narrow `def` only, deliberately different from gallery's broader `definitionCount: 16`)
- `sorryCount: 0` ✓

These two conventions diverge intentionally on `theoremCount` semantics
when private-lemma differs (gallery uses broad, research JSON has used
narrow historically; mechanic-canonical now uses raw broad — see #19934 /
#19840 / #19885). The S4 ship aligns the research JSON to the
mechanic-canonical raw broad convention so future mechanic batches do not
re-flag this slug.

---

## §4. Host snapshot (S4 time)

| Surface | Value | Status | Notes |
|---------|-------|--------|-------|
| Disk free (`/` boot vol) | 4.6 Gi avail | 🔴 RED | Below 5 Gi soft floor. Cross-validated by erdos-1183 S4 #20120 (354 MiB earlier this window — disk has recovered slightly) and minkowski-theorem S29 #20018 (3.4 Gi T−1h ago). Trend is RED-leaning across this STATE-SYNC cohort. |
| Disk free (Data vol `/System/Volumes/Data`) | 4.6 Gi avail | 🔴 RED | Same as above. |
| Docker daemon (`docker info` Server section) | empty (client info OK; Server section returns empty after ≥10 s) | 🔴 RED | Server hung / unresponsive. Matches G8 cumulative ≥21h carry-forward (per researcher-3 erdos-1183 S4 memo and four-square S27 memo). |
| `proofs/.lake` | `→ /Users/rwalters/GitHub/lean-genius/proofs/.lake` (self) | 🔴 RED | G9 self-cycle confirmed, ≥9d standing. |
| Mathlib SHA (`proofs/lake-manifest.json`) | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) | ✅ GREEN | Byte-stable ≥54h+ across the 7+ STATE-SYNC cohort (matches sibling memos in MEMORY.md: minkowski S29, four-square S27, prob-method S9, erdos-1151 S34, erdos-1183 S4). |
| Branch base | `origin/main` (post-reset; fresh `git fetch origin main` + `git checkout -b research/erdos-1071-s4-statesync-long-completed-drift-catchup origin/main`) | ✅ GREEN | Clean diff: 3 files. |

**3 RED INFRA blockers** foreclose any ACT this session. Doc-only S4 is
the only safe iteration. As with erdos-1183 S4: this slug has **no
pending Lean work** anyway (#10880 closed the formalization with the
deliberate 1-axiom split), so the INFRA RED is academic — but ship is
still correct because the registry-side drift is well above the
release-without-PR threshold.

---

## §5. Bearer spot-check (proof engine surface)

Per the SHA-stable-Mathlib busywork-avoidance memory, no full 5-9 bearer
re-walk on a Mathlib pin that has been byte-stable ≥54h. Targeted spot
checks on the four most recently-added bearers from #10880:

**Bearer 1**: `exists_maximal_packing`
**Location**: `proofs/Proofs/Erdos1071Problem.lean:261`
**Signature**: `theorem exists_maximal_packing : ∃ S : Set UnitSegment, IsMaximalPacking S`
**Status**: ✅ GREEN, present, file SHA-stable since 2026-04-21.

**Bearer 2**: `packing_chain_union` (private lemma)
**Location**: `proofs/Proofs/Erdos1071Problem.lean:244`
**Status**: ✅ GREEN, present, used by Zorn invocation in `exists_maximal_packing`. This is the lemma the research-JSON narrow `^lemma ` regex missed (line 11 of §2).

**Bearer 3**: `maximal_iff_not_extendable`
**Location**: `proofs/Proofs/Erdos1071Problem.lean:231`
**Status**: ✅ GREEN, present.

**Bearer 4 (axiom)**: `danzer_finite_maximal_packing`
**Location**: `proofs/Proofs/Erdos1071Problem.lean:295`
**Status**: ✅ GREEN (still 1 axiom, byte-stable since 2026-04-21).

No cross-cite drift inferred. Mathlib pin unchanged. File untouched since
2026-04-21 (no commits between #10880 and S4 on this file).

---

## §6. Readiness gates (post-S4 forecast)

| Gate | Pre-S4 status | Post-S4 status | Notes |
|------|---------------|----------------|-------|
| A. Lean build clean | ✅ (#10880 implicit by deployer-acceptance) | ⚠️ unknown live | Docker hung; deferred to next live build. |
| B. 0 sorries | ✅ | ✅ | `grep -cE '\bsorry\b' = 0` |
| C. Axiom count consistent | ✅ (1) | ✅ (1) | `grep -c '^axiom ' = 1` matches all three JSON surfaces. |
| D. Bearer SHA-stability | ✅ | ✅ | Spot-check §5 |
| E. Gallery meta consistent | ✅ | ✅ | All 6 numeric fields match `wc -l` / `grep` canonical. |
| F. Research JSON consistent | ❌ (≥11 drifts) | ✅ | This PR fixes. |
| G. Mathlib pin unchanged | ✅ | ✅ | `2df2f0150c…` |
| H. State.md mirrors registry COMPLETED | ❌ (`NEW`) | ✅ | This PR rewrites. |
| I. Sessions/ bootstrapped | ❌ (none) | ✅ | This file. |
| J. Pool entry agrees with registry | ❌ (`in-progress` despite registry `graduated` since 2026-03-24) | ✅ (post-PR `claim-problem.sh update completed`) | Re-flip after registry-side catchup lands. |
| K. Disk floor | 🔴 4.6 Gi | 🔴 4.6 Gi | Persistent INFRA RED, ship-anyway under doc-only qualifier. |

---

## §7. Sibling INFRA cross-validation

Per the *3-RED INFRA* memory cohort (G7 disk, G8 Docker hung, G9 `.lake`
self-cycle), this S4 ships under the same window as several recent
STATE-SYNC PRs which were all accepted by the deployer:

| Sibling PR | Slug | Author | T-offset | Disk free reported | Docker | `.lake` |
|------------|------|--------|---------|-------------------|--------|---------|
| #20120 | erdos-1183 S4 STATE-SYNC | researcher-3 | T−57 min | 354 MiB (RED-er) | RED hung | RED self-loop |
| #20085 | schauder-fixed-point S25 STATE-SYNC | researcher-4 | T−1h57m | 2.0 Gi | RED hung | RED self-loop |
| #20072 | four-square-distribution S27 STATE-SYNC | researcher-4 | T−2h27m | 2.9 Gi | RED hung | RED self-loop |
| #20018 | minkowski-theorem S29 STATE-SYNC | researcher-4 | T−3h13m | 3.4 Gi | RED hung | RED self-loop |
| #20007 | erdos-1151 S34 STATE-SYNC | researcher-11 | T−3h41m | 5.2 Gi (just above floor) | RED hung | RED self-loop |

All five were merged. Disk has trended down across this window and
recovered marginally just before S4. The doc-only qualifier remains
ship-appropriate.

---

## §8. Post-merge action plan

After PR merges:

1. `bash /Users/rwalters/GitHub/lean-genius/scripts/research/claim-problem.sh update erdos-1071 completed`
   — flips `.lean/state/candidate-pool.json` for this slug from
   `status: in-progress` → `status: completed`, generates stats signal.
2. Cleanup branch:
   `git checkout main && git worktree run … && git branch -D research/erdos-1071-s4-statesync-long-completed-drift-catchup`
   (driven from the parent worktree).
3. Update local MEMORY.md (researcher-10 cycle log): record this as a
   "first-claim of cycle lands on long-completed slug + ship doc-only
   S{N+1} STATE-SYNC + post-merge pool flip" instance, distinct from
   the erdos-1183 instance only by (a) the predecessor-Lean-PR is
   #10880 not #13816, (b) the registry was already graduated *before*
   the predecessor Lean PR (graduation 2026-03-24, predecessor Lean PR
   2026-04-21, both pre-state-md-update), and (c) the slug retains 1
   axiom (Danzer) rather than 0.

No followup PR planned: gallery `meta.json` is already canonical, sibling
slugs (`erdos-1071-oq-01`) were graduated separately on 2026-03-24 and
should be independently audited if drift is later detected on them.

---

## §9. Honesty calibration

- **What S4 changes**: 3 doc-only files. Zero Lean. Zero gallery
  `meta.json`. Zero sibling-slug edits. Zero new theorems / axioms /
  sorries.
- **Build status**: not re-built (Docker hung; G7 disk RED). Bearer
  spot-checks rely on file-level SHA stability since 2026-04-21 (no
  commits on `proofs/Proofs/Erdos1071Problem.lean` in that 26-day window).
- **Iteration accounting**: I am calling this S4 (research JSON had
  iter=3; state.md had iter=1 stale; gallery contributions span four
  PRs but the slug's "session" semantics in research/ have been opaque
  since the project's pre-2026-03 sessions/ convention). S4 = +1 over
  the more credible of the two priors (research JSON's 3).
- **What S4 does not claim**: it does not claim the slug is `verified`
  (it isn't — 1 Danzer axiom). It does not claim Part (b) of Erdős'
  question is resolved (it isn't — only stated). It does not claim a
  fresh Lean build was run (none was). It explicitly carries the 1-axiom
  honest assessment in `currentState.blockers` and in the
  `progressSummary` refresh.
