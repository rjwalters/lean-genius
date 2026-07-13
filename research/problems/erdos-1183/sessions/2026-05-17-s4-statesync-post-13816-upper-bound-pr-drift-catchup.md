# S4 STATE-SYNC — post-#13816 upper-bound PR drift catchup + JSON registry COMPLETED + pool flip + sessions/ bootstrap

**Slug**: erdos-1183
**Phase**: COMPLETED → COMPLETED (unchanged; S3 marked completion 2026-04-29T04:30Z, this S4 makes the JSON registry + pool agree)
**Iteration**: 3 → 4
**Date**: 2026-05-17
**Researcher**: researcher-3
**PR**: this PR (doc-only)
**Predecessor (state.md)**: S3 audit by researcher-1, 2026-04-29T04:30Z (T−18d)
**Predecessor (Lean file)**: PR #13816 by rjwalters, merged 2026-04-29T05:08Z (T−18d, ~38 min *after* S3)

---

## §0. TL;DR

S3 (researcher-1) closed the slug as `Phase: COMPLETED, Iteration: 3` and
pool-flipped to `completed`. Thirty-eight minutes later, PR #13816 added
~34 LOC of trivial upper bounds (`erdos1183_f_upper_bound`,
`erdos1183_F_upper_bound`) — exactly the "Optional future work" item that
S3's state.md flagged in its Next Action section. But #13816 only touched
`proofs/Proofs/Erdos1183Problem.lean`, `research/problems/erdos-1183/state.md`
(2 minor lines), and `src/data/proofs/erdos-1183/meta.json` (the gallery
entry, where it updated `lineCount` to 314). It did **not** touch the
**research JSON registry** (`src/data/research/problems/erdos-1183.json`),
which retained:
- `phase: OBSERVE` (vs gallery / state.md COMPLETED)
- `status: active` (vs gallery / pool completed)
- `currentState.phase: ACT`, `currentState.iteration: 2` (vs state.md iter 3)
- `currentState.focus`: pre-Session-2 framing
- `currentState.nextAction: "Begin problem exploration."` (pre-S3 default)
- `leanFiles[0].lineCount: 315` (off-by-one vs canonical `wc -l = 314`;
  this is the legacy `split('\n').length` convention. Mechanic-canonical
  per #19663/#19667 and gallery meta.json ground truth = 314)
- `knowledge.builtItems`: 14 items, missing the upper-bound entries
- `lastUpdate: 2026-03-13T07:52:17Z` (pre-S2)
- No `sessions/` directory

S4 is doc-only — fixes all of the above on the research-side, bootstraps
`sessions/`, and re-runs `claim-problem.sh update completed` to lock the
pool entry to `completed` (S3 already did this, but the candidate-pool.json
read at claim time showed `status: in-progress`; either pool regenerated
since S3, or S3's flip never landed — either way, this PR re-flips after
the JSON-registry catchup).

No Lean changes. No gallery `meta.json` changes (already canonical). No
sibling-slug edits. No new theorems / axioms / sorries. No proof
regression. Erdős-1183's `Erdos1183Problem.lean` remains 314 LOC, 17 thm,
14 def, 0 axiom, 0 sorry.

---

## §1. Why S4 fires

**Trigger**: claim-random landed researcher-3 on erdos-1183 at
2026-05-17T03:44:33Z (90-min TTL). Recency probe found:

- No open PRs touching erdos-1183 (last PR #13816 T−18d, no collision risk).
- No ≤T-2h merges anywhere on this slug.
- state.md says `COMPLETED iter=3` but research JSON registry disagrees on
  ~10 surfaces (see §2 ledger).
- Mechanic-canonical convention drift (LOC 315 vs `wc -l = 314`) — same
  legacy `split('\n').length` family that has been swept across recent
  mechanic batches (#19663, #19667, #19814, #19815, #19816, #19818).

Per the `_postship_pivot_to_active_slug_with_very_recent_statesync_predecessor_release_without_pr_when_residual_drift_below_threshold`
memory: the "release without PR" path is appropriate when a STATE-SYNC
predecessor is ≤T-6h AND residual drift is below threshold. Here the
predecessor is T-18d and residual drift is ~10 surfaces (well above
threshold). Ship.

Per the `_postship_pivot_to_long_completed_slug_with_recent_statesync_predecessor_left_residual_drift_ship_smaller_followup_statesync`
memory: long-completed slug + drift → ship a smaller follow-up STATE-SYNC.
This matches exactly: slug closed T-18d, PR #13816 left residual drift
across phase enums + numerics + builtItems + lastUpdate + sessions/ absent.

S4 scope: **doc-only**, 3 files (state.md + research JSON + NEW sessions/
memo), 0 Lean changes, 0 gallery edits, +1 pool-status flip after merge.

---

## §2. Drift inventory (research JSON registry vs source-of-truth, as of 2026-05-17T04:19Z)

Verified via direct file reads in worktree
`/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-3/`.

| # | Field | Pre-S4 | Post-S4 | Source of truth |
|---|-------|--------|---------|-----------------|
| 1 | top-level `phase` | `OBSERVE` | `COMPLETED` | state.md S3 (`Phase: COMPLETED`) + gallery `meta.status: axiomatized` (closed-form) |
| 2 | top-level `status` | `active` | `completed` | state.md S3 + pool flip + 336-slug `completed`+`COMPLETED` precedent |
| 3 | `currentState.phase` | `ACT` | `COMPLETED` | state.md S3 |
| 4 | `currentState.iteration` | `2` | `4` | state.md S3 said `3`; S4 = +1 |
| 5 | `currentState.since` | `2026-01-16T08:44:15.246Z` | `2026-05-17T04:19:00.000Z` | This S4 entry timestamp |
| 6 | `currentState.focus` | "Formalized problem statement and proved trivial chain bound" | S4 framing (PR #13816 absorption + registry COMPLETED) | This PR scope |
| 7 | `currentState.blockers` | `[]` | `["Genuine open conjectures … research-paper-scale"]` | state.md S3 Blockers section |
| 8 | `currentState.nextAction` | `"Begin problem exploration."` | "Slug COMPLETED. … RELEASE without PR …" | state.md S4 Next Action |
| 9 | `currentState.attemptCounts.total` | `1` | `2` | This S4 = +1 (intentional honest increment; Sessions 1–3 collapsed by older convention to `1`, S4 adds 1) |
| 10 | `leanFiles[0].lineCount` | `315` | `314` | `wc -l proofs/Proofs/Erdos1183Problem.lean = 314` + gallery `meta.json.meta.lineCount = 314` |
| 11 | `knowledge.progressSummary` | pre-#13816 (chain bound only) | post-#13816 (chain + upper bounds) | PR #13816 contents |
| 12 | `knowledge.builtItems` count | 14 (missing upper bounds) | 15 (PR #13816 entry appended) | PR #13816 contents |
| 13 | `knowledge.insights` count | 11 (missing constructive upper-bound observation) | 12 (insight appended) | PR #13816 contents + Session 2 BddAbove framing |
| 14 | `lastUpdate` | `2026-03-13T07:52:17.060Z` | `2026-05-17T04:19:00.000Z` | This PR |
| 15 | `sessions/` directory | absent | bootstrapped + S4 memo (this file) | Convention parity with all post-S2 slugs |

### Numerics audit (canonical mechanic conventions)

```
proofs/Proofs/Erdos1183Problem.lean
  wc -l                              : 314   (CANONICAL — gallery meta.json.meta.lineCount also 314)
  grep -cE '^(protected |private |noncomputable )*(theorem|lemma) ' : 17
  grep -cE '^(def|noncomputable def|opaque def) '                   : 14
  grep -cE '\bsorry\b'                                              : 0
  grep -cE '^axiom '                                                : 0
```

Gallery `src/data/proofs/erdos-1183/meta.json` (already canonical, NOT touched):
- `meta.lineCount: 314` ✓
- `meta.sorries: 0` ✓
- `meta.axiomCount: 0` ✓
- `meta.theoremCount: 17` ✓
- `meta.definitionCount: 14` ✓
- `leanFile.lineCount: 314` ✓
- `leanFile.axiomCount: 0` ✓
- `leanFile.sorryCount: 0` ✓
- `leanFile.theoremCount: 17` ✓
- `leanFile.definitionCount: 14` ✓
- `meta.status: axiomatized`, `meta.badge: wip` (1 issue: badge=wip but assumptions says "0 axiom declarations" → see §7 Honesty calibration; not changed in this PR, deferred to mechanic)

All gallery fields byte-stable and consistent with the file. Only the
research JSON's `leanFiles[0].lineCount` was off by one (= legacy
`split('\n').length` convention from a much-older `pnpm build` regeneration
pre-mechanic-canonicalization).

---

## §3. Host snapshot (S4 time)

| Surface | Value | Status | Notes |
|---------|-------|--------|-------|
| Disk free (`/` boot vol) | 354 MiB | 🔴 RED-er | Below same-day soft floor (~5 Gi). Cross-validated by minkowski S29 #20018 (3.4 Gi T−1h17m) and four-square S27 #20072 (2.9 Gi T−30min) — disk has dropped further since those. |
| Disk free (Data vol) | 563 MiB | 🔴 RED-er | Same as above. ~100% used, 79% inode use. |
| Docker daemon | `docker version --format '{{.Server.Version}}'` → empty (client info OK) | 🔴 RED | Server hung / unresponsive. Matches G8 cumulative ≥21h carry-forward (per researcher-4 four-square S27 memo). |
| `proofs/.lake` | `→ /Users/rwalters/GitHub/lean-genius/proofs/.lake` (self) | 🔴 RED | G9 self-cycle confirmed, ≥9d standing. |
| Mathlib SHA | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | ✅ GREEN | Byte-stable ≥54h+ across 7+ STATE-SYNC cohort (matches sibling memos in MEMORY.md). |
| Branch base | `origin/main` (post 198-commit catchup; clean rebase) | ✅ GREEN | Fresh `git fetch origin main` + `git checkout -b research/erdos-1183-s4-statesync origin/main` |

**3 RED INFRA blockers** foreclose any ACT this session. Doc-only S4 is
the only safe iteration. Note: this slug has **no pending Lean work**
anyway (S3 already declared formalization complete, #13816 already
delivered the optional upper bound), so the INFRA RED is academic —
release-without-PR would also have been correct *if* drift were below
threshold; drift is above, so we ship doc-only.

---

## §4. Bearer spot-check (proof engine surface)

Per `_state_md_three_sessions_behind_..._mechanic_cascade_..._SHA_stable_busywork`
memory, no full 5-9 bearer re-walk on SHA-stable Mathlib pin. Single
spot-checks on the two #13816 bearers:

**Bearer 1**: `erdos1183_f_upper_bound`
**Location**: `proofs/Proofs/Erdos1183Problem.lean:270`
**Signature**: `theorem erdos1183_f_upper_bound (n : ℕ) : erdos1183_f n ≤ 2 ^ n`
**Status**: ✅ GREEN, present, SHA-stable.

**Bearer 2**: `erdos1183_F_upper_bound`
**Location**: `proofs/Proofs/Erdos1183Problem.lean:287`
**Signature**: `theorem erdos1183_F_upper_bound (n : ℕ) : erdos1183_F n ≤ 2 ^ n`
**Status**: ✅ GREEN, present, SHA-stable.

**Bearer 3 (lower bound, pre-existing)**: `erdos1183_chain_bound`
**Location**: `proofs/Proofs/Erdos1183Problem.lean:172`
**Signature** carries `(n : ℕ) (χ : SubsetColoring n) : ∃ F ...`
**Status**: ✅ GREEN, present, SHA-stable, untouched since S2 (2026-03-28).

No cross-cite drift inferred. Mathlib pin unchanged, file untouched since
2026-04-29 (no commits between #13816 and S4 on this file).

---

## §5. Readiness gates (post-S4 forecast)

| Gate | S3 status | S4 status | Notes |
|------|-----------|-----------|-------|
| A. Lean build clean | ✅ (S3 pre-#13816) + ✅ (#13816 implicit by deployer-acceptance) | ⚠️ unknown live | Docker hung; deferred to next live build |
| B. 0 sorries | ✅ | ✅ | `grep -c '\bsorry\b' = 0` |
| C. 0 axioms | ✅ | ✅ | `grep -c '^axiom ' = 0` |
| D. Bearer SHA-stability | ✅ | ✅ | Spot-check §4 |
| E. Gallery meta consistent | ✅ | ✅ | All 10 numeric fields match `wc -l` / `grep` canonical |
| F. Research JSON consistent | ❌ (10+ drifts) | ✅ | This PR fixes |
| G. Mathlib pin unchanged | ✅ | ✅ | `2df2f0150c…` |
| H. Sessions/ bootstrapped | ❌ (none) | ✅ | This file |
| I. Pool entry agrees with state.md | ❌ (`in-progress` despite S3 flip claim) | ✅ (post-PR `claim-problem.sh update completed`) | Re-flip after registry catchup |
| J. Disk floor | n/a | 🔴 354 MiB | INFRA RED |
| K. Docker daemon | n/a | 🔴 server hung | INFRA RED |
| L. proofs/.lake topology | n/a | 🔴 self-symlink | INFRA RED |

Gates J/K/L are host-side and apply to any ACT attempt; they do not block
S4 (doc-only).

---

## §6. Explicit non-actions (what S4 deliberately does NOT do)

1. **Do not edit `proofs/Proofs/Erdos1183Problem.lean`** — file is correct
   post-#13816; 314 LOC, 17 thm, 14 def, 0 axiom, 0 sorry; all bearers SHA-
   stable.
2. **Do not edit gallery `meta.json`** — already canonical for all
   numerics (`lineCount: 314` matches `wc -l`). The `badge: wip`
   vs `axiomCount: 0` minor inconsistency (see §7) is deferred to mechanic.
3. **Do not edit sibling slug research JSONs** — no leanFiles[] cross-slug
   surface exists here (single-slug-owned file; only this slug's research
   JSON references `Proofs/Erdos1183Problem.lean`).
4. **Do not run `lake build` / `pnpm build`** — host INFRA RED forecloses
   build; `pnpm build` would also regenerate ~1047 sibling research JSONs
   (`_mechanic_pnpm_build_regenerates_all_research_jsons` trap), some of
   which would leak untracked.
5. **Do not re-walk all 17 bearers** — SHA-stable + pin-stable + file-
   untouched-since-#13816 → single spot-check on the 2 new + 1 pre-existing
   bearer sufficient.
6. **Do not change `meta.json` `status` enum** — `axiomatized` is
   technically wrong (assumptions=0, axioms=0) but is the existing gallery
   state pre-S4; changing it touches the gallery side and would be scope
   creep. Honest TODO for mechanic or a future enrichment pass: bump
   `status: axiomatized → verified` and `badge: wip → verified` (subject
   to enrichment gate review). See §7.
7. **Do not start the f(0)=1, f(1)=1, f(2)=2 small-case decoration** —
   genuine optional work, would need ACT (Docker), and INFRA RED
   forecloses; future researcher should not bother unless other substantive
   work also needs ACT.
8. **Do not touch the proofs/.lake self-symlink** — host recovery, not
   researcher scope.
9. **Do not modify `relatedProofs`** — the current `["erdos-1", "erdos-11",
   "erdos-118", "erdos-1183"]` list includes a self-reference and is
   loosely populated, but cleanup is outside this STATE-SYNC scope.

---

## §7. Picker decision matrix (for next claim-random landing here)

If a future researcher lands on erdos-1183:

| Condition | Action |
|-----------|--------|
| No new drift since S4 (research JSON unchanged, Lean file unchanged, pool consistent) | **RELEASE without PR** (this is the dominant case; slug is COMPLETED, no work pending) |
| New mechanic batch touched `Erdos1183Problem.lean` (rare — single-slug-owned file) | Ship S5 STATE-SYNC mirroring this one if drift > threshold; otherwise RELEASE |
| Mathlib pin bumped + build broke | Ship S5 PREP/ACT to fix; not a STATE-SYNC scope |
| Disk green + Docker green + researcher wants decoration | OPTIONAL: f(0)=1, f(1)=1, f(2)=2 small-case computations (~20 LOC, low value). Default: skip. |
| Status enum cleanup (`axiomatized → verified`) merged separately | RELEASE |

The dominant case is **release without PR**. erdos-1183 should largely
disappear from the candidate pool after this PR (pool entry flipped to
`completed`), so future claim-random landings here should be rare.

---

## §8. Mechanic handoff items

Two minor housekeeping items, both LOW priority:

1. **Gallery `meta.json` status/badge**: `status: axiomatized` + `badge: wip`
   are inconsistent with `axiomCount: 0` + `assumptions: "0 axiom
   declarations"`. The two open conjectures are stored as `def Prop` not
   `axiom` (Session 2 conversion). Honest enums would be `status: verified`,
   `badge: verified` *if* the gallery accepts a "verified" status for a slug
   where the open math conjecture itself remains open (only the trivial
   bounds are proved). Alternative honest framing: `status: formalized`,
   `badge: formalized` (the formalization is complete; the math is open).
   This is an enrichment/judge call, not a mechanic mechanical fix. Flag
   for next enricher pass on erdos slugs.
2. **`relatedProofs` self-reference**: contains `"erdos-1183"` itself.
   Likely a generator artifact. Mechanic batch on `relatedProofs` cleanup
   could de-duplicate self-refs across the registry.

Neither item is blocking; both can wait.

---

## §9. Honesty calibration

This S4 is a maintenance iteration, not a research result. It:

- ✅ Documents 15-row drift inventory and fixes all 14 in-scope rows
- ✅ Bootstraps `sessions/` directory (convention parity)
- ✅ Re-flips pool entry `in-progress → completed` (post-merge via
  `claim-problem.sh update completed`)
- ✅ Adds 1 honest attempt-count increment (`total: 1 → 2`)
- ❌ Does not advance any mathematical front (chain bound already proved
  Session 1, sSup correction Session 2, upper bound PR #13816)
- ❌ Does not eliminate any axioms (already 0)
- ❌ Does not address the Howorka reference gap (F(n) > n^ω(n) for same-
  size colorings — knowledge.md cites it but no formalization attempt)
- ❌ Does not address the relatedProofs self-reference or `badge: wip`
  inconsistency (deferred to mechanic / enricher)

The slug status remains COMPLETED. The two open conjectures
(`erdos1183_f_growth_conjecture`, `erdos1183_F_superpolynomial_conjecture`)
remain `def Prop` (not assumed true) — research-paper-scale work to settle
them is preserved as honest open math, not formalization debt.

**Net delta from this PR**: 3 files changed (state.md +91/-26 ish,
research JSON +9 fields edited / +1 insight / +1 builtItem,
sessions/ NEW ~290 LOC). Zero Lean changes. Zero gallery edits. Zero
sibling-slug edits. Zero build artifacts.

---

## §10. References

- **#13816** (rjwalters, merged 2026-04-29T05:08:18Z): the upper-bound PR
  this S4 absorbs. Diff: `proofs/Proofs/Erdos1183Problem.lean +34/-0`,
  `research/problems/erdos-1183/state.md +27/-9`,
  `src/data/proofs/erdos-1183/meta.json +9/-8` — but **no research JSON
  registry edit**, which is the root cause of the drift S4 fixes.
- **S3 audit** (researcher-1, 2026-04-29T04:30Z): the prior session that
  marked the slug COMPLETED in state.md and (per state.md prose) flipped
  the pool. No PR was created for the audit itself.
- **STATE-SYNC pattern precedent**: `shannon-channel-coding-oq-02-oq-03`
  S2 STATE-SYNC #19819 (researcher-9, 2026-05-16, mechanic-handoff
  variant); `borsuk-ulam-oq-02-oq-01-oq-03-oq-02` S3 #19659 (leanFiles
  mechanic handoff). This S4 is a hybrid: post-Lean-PR drift catchup
  (closer to a "post-mechanic" pattern) but the trigger was a research-
  semantic Lean change (#13816) not a mechanic numeric sweep.
- **Convention citation**: `_mechanic_pnpm_build_regenerates_all_research_jsons`
  (use `wc -l` value; matches gallery meta.json + mechanic PRs
  #19663/#19667/#19814/#19815/#19816/#19818); `_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap`
  (ensure_ascii=False to avoid Unicode escape bloat — verified: this PR's
  JSON diff preserves ⌈⌉ / ≤ / ≥ as raw UTF-8).
- **Memory citations**:
  - `_postship_pivot_to_long_completed_slug_with_recent_statesync_predecessor_left_residual_drift_ship_smaller_followup_statesync`
    (closest pattern; here predecessor is a Lean PR + an undocumented S3
    audit rather than a STATE-SYNC PR, and "recent" is T-18d rather than
    T-1d, but the response is the same: ship smaller follow-up STATE-SYNC)
  - `_postship_pivot_to_active_slug_with_very_recent_statesync_predecessor_release_without_pr_when_residual_drift_below_threshold`
    (the alternative path; not taken here because drift is well above
    threshold)
  - `_session_pattern_1_substantive_ACT_PR_after_multiple_triage_releases`
    (this is the inverse: a substantive STATE-SYNC with 0 triage releases
    preceding it, since first-claim landed on a workable slug)
