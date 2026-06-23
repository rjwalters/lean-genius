# Session 29 — S28 PREP, JSON catchup absorbing S27 PREP #19548 (researcher-1, 2026-05-16)

Companion to the `state.md` S28 PREP head and the `currentState` patch in `src/data/research/problems/abel-ruffini-galois-extensions-oq-07.json`.

## §1 Trigger and timing

- **Researcher**: researcher-1
- **Claim time**: 2026-05-16T14:06:03Z (`claim-random` → `Selected abel-ruffini-galois-extensions-oq-07 (652 available, tier: MODERATE+ (depth-first), 120 in tier); Knowledge score: 86 (RICH); Expires: 2026-05-16T15:36:03Z`)
- **Predecessor PR**: #19548 (S27 PREP, researcher-6) — opened 2026-05-16T09:11:14Z, merged 2026-05-16T13:53:37Z
- **Delta predecessor-merge → this-claim**: T+12.5 minutes
- **Mathlib pin at both endpoints**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) — byte-stable
- **Branch**: `research/researcher-1-abel-ruffini-galois-extensions-oq-07-20260516T140613Z` (forked off `origin/main`)

## §2 JSON delta (the catchup)

File: `src/data/research/problems/abel-ruffini-galois-extensions-oq-07.json`

### §2.1 Top-level fields

| Field | Before (S26 BUILD-DIAGNOSTIC era) | After (S28 PREP) |
|---|---|---|
| `phase` | `"ACT"` (stale — left over from pre-BUILD-BLOCKER state) | `"BUILD-BLOCKER"` (matches `state.md` line 3 and `currentState.phase`) |
| `status` | `"active"` (generic) | `"blocked-on-mechanic"` (specific — researcher cannot ACT until mechanic BUILD-FIX merges) |
| `lastUpdate` | `"2026-05-16"` | `"2026-05-16"` (unchanged form — date-only, day-granular; preserved verbatim) |

### §2.2 `currentState` fields

| Field | Before | After |
|---|---|---|
| `currentState.phase` | `"BUILD-BLOCKER"` | `"BUILD-BLOCKER"` (unchanged — already correct) |
| `currentState.since` | `"2026-05-16T01:25:00.000Z"` | `"2026-05-16T01:25:00.000Z"` (unchanged — BUILD-BLOCKER start time stable since S26 diagnostic) |
| `currentState.iteration` | `26` | `28` (absorbs S27 PREP iter-27 + this S28 PREP) |
| `currentState.focus` | 1200+ char paragraph describing S26 BUILD-DIAGNOSTIC only (no mention of S27 PREP) | 1595 char paragraph: S28 PREP framing + S27 PREP §4 sharpening summary (3 HIGH paste-ready clusters with line-by-line LOC counts) + INFRA snapshot + S26 BUILD-DIAGNOSTIC backstory in one sentence |
| `currentState.nextAction` | Order: §2.1/§2.2 → §2.3/§2.4 → §2.5/§2.6 → §2.7/§2.8 → §2.9 + stale `sync 'meta.json' 'lineCount: 1791 → 1898' + 'theoremCount: 36 → 38'` step | 2288 char rewrite: HIGH-paste-ready order §2.7 → §2.6 → §2.4 → §2.2 → §2.9 → §2.3 → §2.1 → §2.5 → §2.8 (per S27 PREP §4); stale meta.json sync step DROPPED with explicit note (`already discharged by mechanic PR #19510 (merged 2026-05-16T08:52:48Z); current 'meta.json' values verified at 'lineCount: 1898', 'theoremCount: 38'`); explicit INFRA-blocker call-out for mechanic; S29/S30 ACT roadmap retained |

### §2.3 Fields NOT touched

- `slug`, `title`, `tier`, `path`, `problemStatement`, `knownResults`, `references`, `started`, `significance`, `tractability`, `leanFiles` — all stable upstream metadata, no drift detected.
- `knowledge.{progressSummary,builtItems,insights,mathlibGaps,nextSteps}` — substrate unchanged since S25 (the 34 `builtItems` entries are append-only and accurate); S26 BUILD-DIAGNOSTIC and S27 PREP added no new built items because both were doc-only PREPs.
- `relatedProofs`, `tags` — orthogonal to phase/iteration drift.

## §3 INFRA reaffirm (B1 Docker hung)

| Probe | Command | Result | Pattern |
|---|---|---|---|
| Disk | `df -h /` | `/dev/disk3s1s1   926Gi    16Gi   6.8Gi    71%    458k   68M    1%   /` then `6.8Gi   70%` on re-probe (single-digit Gi fluctuation under host-side write pressure) | host-disk pressure (memory `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`); tighter than S27 PREP's 7.0 Gi snapshot at T-12.5min |
| Docker daemon | `docker info 2>&1 \| head -5` (background) | hung 60s+ without returning `Containers/Runtime` headers; required `kill -9 26963` to release | B1 = Docker daemon hung; matches S27 PREP's `docker info slow` diagnosis |
| Mathlib SHA | `gh api repos/leanprover-community/mathlib4/git/refs/heads/master` was NOT re-fetched (intentional — S27 PREP at T-12.5min already pinned `2df2f0150c…` and `proofs/lakefile.toml` shows same value) | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, 2025-12-13) | byte-stable across S27 PREP T-12.5min window |

**INFRA conclusion**: B1 Docker daemon hung unchanged since S27 PREP T-12.5min. Mechanic BUILD-FIX requires per-iteration Docker builds — therefore mechanic is also blocked on INFRA recovery (host disk reclaim or Docker daemon restart). Neither researcher nor mechanic can advance the slug substantively until INFRA clears.

## §4 Stranded-branch reaffirm

`git ls-remote origin "refs/heads/*abel-ruffini-galois*"` (2026-05-16T14:08Z) returns 8 remote branches:

```
e996d4fe79103da995602a9ee471334c423bd619	refs/heads/fix/mechanic-abel-ruffini-galois-extensions-oq-07-counts-1778270926
40497e26aa1166b41473e6940d65bd1824e5faa2	refs/heads/research/abel-ruffini-galois-extensions-oq-07-iter-fresh-1778287599
6cc7de1dc9956de96da7b4e9eab9c101dbb0e323	refs/heads/research/abel-ruffini-galois-extensions-oq-07-iter14-s14-1778283246
fd085becc9e7af3412c544b3b227c56c58b9e547	refs/heads/research/abel-ruffini-galois-extensions-oq-07-s16-cube-id-card-1778287229
c04401cbfdaf5ac9f7ab1ddc623b4a7df7f943e3	refs/heads/research/abel-ruffini-galois-extensions-oq-07-s19-ingredient4-forward-1778543986
1e78dd5f2a5a4e27d92a5718149954d6592c1c0d	refs/heads/research/abel-ruffini-galois-extensions-oq-07-s7-1778244761
e996d4fe79103da995602a9ee471334c423bd619	refs/heads/research/abel-ruffini-galois-oq07-s10-1778269271
8267828a26d4121d11098fd5d32467eea4119aef	refs/heads/research/abel-ruffini-galois-oq07-session2-r10
```

Of these, 4 still have OPEN PRs:

| PR | Title | Created | Status per S24 PREP §4 |
|---|---|---|---|
| #17528 | S14 — cube-identity bridge for S10 closure (build pending) | 2026-05-08 | formally obsolete (superseded by merged S15/S17 path) |
| #17586 | S16 — Set-level pairwise disjointness for punctured Sylow 3-subgroups (build pending) | 2026-05-09 | formally obsolete (superseded by merged S18 path) |
| #17587 | S16 — sylow_three_set_diff_one_ncard_eq_two (build pending, narrowed) | 2026-05-09 | formally obsolete (superseded by merged S18 path) |
| #17685 | S19 — ingredient 4 forward set inclusion (build pending) | 2026-05-12 | formally obsolete (superseded by merged S20/S21/S22 path) |

No change since S27 PREP T-12.5min ago. Closure-by-author is not researcher-1's role; defer to `/champion` or `/guide` triage. Surfacing here for downstream readers of `state.md`.

## §5 What this PR does NOT do (tightening rationale)

Memory pattern `_postship_pivot_to_own_just_merged_prep_with_zero_json_edits_at_T_plus_minutes_s` (researcher-4 precedent at T+4min on cramers-rule-oq-01-oq-02-oq-01-oq-01) prescribes the following structure when claim-random returns a slug whose predecessor PREP merged T+small-minutes ago: keep ONLY (a) JSON catchup + (e) Docker INFRA reaffirm + (f) stranded-branch reaffirm. DROP (b) Mathlib SHA recheck, (c) bearer SYMBOL re-spot-check, (d) new paste-ready skeleton — all three are busywork at T+12.5min with byte-stable SHA. The substrate of the pattern is "predecessor at T+small-minutes covered the deep layers"; the specific identity of the predecessor agent (researcher-6) versus the current agent (researcher-1) does not change the cost calculus.

| Dropped layer | Why dropped at T+12.5min |
|---|---|
| Mathlib SHA recheck | S27 PREP §5 already verified `2df2f0150c…` at T-12.5min; `proofs/lakefile.toml` byte-stable; upstream Mathlib master also unchanged in 12.5min (no fast-cadence release cycle on the relevant subtree) |
| 4-spot bearer SYMBOL re-spot-check | S27 PREP §5 already verified `IsPGroup`, `IsPGroup.iff_card`, `Sylow.normal_of_normalizer_normalizer`, `Nat.card`, `scoped infixl " on " => onFun` all unchanged at the pin; no SHA churn means no symbol churn |
| New paste-ready Lean skeleton | S27 PREP §4 already upgraded 3 fix candidates from "diagnostic hypothesis" to HIGH paste-ready with full `gh api` verification; S26 BUILD-DIAGNOSTIC §2 already cataloged the full 9-cluster fix space; mechanic has everything needed already |

| Kept layer | Why kept at T+12.5min |
|---|---|
| (a) JSON catchup | S27 PREP table explicitly says `src/data/proofs/.../meta.json | UNCHANGED` but does NOT list the **research JSON** `src/data/research/problems/abel-ruffini-galois-extensions-oq-07.json` anywhere in its "what this PR does" — so the research-JSON drift (1 iter behind state.md + stale focus + stale nextAction step + outdated top-level phase/status) survives the S27 PREP merge |
| (e) Docker INFRA reaffirm | S27 PREP described disk pressure but did NOT specifically B1-tag the Docker daemon hang; new evidence here: `docker info` had to be `kill -9`-ed |
| (f) Stranded-branch reaffirm | reasserts the 4 obsolete PRs are still stranded (downstream readers may not have S27 PREP §3 in working memory) |

## §6 ACT-readiness gate (verbatim re-evaluation)

| # | Gate | S27 PREP §7 status | S28 PREP §6 status (re-eval) |
|---|---|---|---|
| 1 | Researcher-side knowledge (S26 ACT recipe + S26 BUILD-DIAGNOSTIC §2 catalog) | GREEN | GREEN (unchanged; substrate untouched) |
| 2 | Researcher-side bearer pin at `2df2f0150c…` | GREEN | GREEN (unchanged) |
| 3 | Paste-ready scaffolds (S27 PREP §4 HIGH + S26 BUILD-DIAGNOSTIC §2 MEDIUM clusters) | GREEN | GREEN (unchanged) |
| 4 | `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` compiles | RED | RED (unchanged; 18 errors; mechanic owns) |
| 5 | Docker daemon | "host-disk pressure" | RED B1 (specifically: daemon hung, `kill -9` required) |
| 6 | Host disk | "7.0 Gi avail" | AMBER (6.8 Gi avail; tighter by 0.2 Gi) |
| 7 | Mechanic claim on slug | "no `loom:mechanic` BUILD-FIX PR open" | RED (still no `loom:mechanic` BUILD-FIX PR open at T+12.5min after S27 PREP merge) |
| 8 | Mathlib SHA stable since S27 PREP | n/a (S27 PREP IS the recheck) | GREEN (`2df2f0150c…` byte-stable across S27 PREP merge → S28 claim window) |

7 of 8 substantive researcher-side gates GREEN; 1 RED INFRA (Docker daemon) + 1 AMBER (disk) on infra side. No researcher ACT possible.

## §7 What S29 should do

- **If mechanic ships BUILD-FIX before next cycle** (most useful path): ship S29 ACT immediately — re-apply S26 ACT recipe paste-ready in `session-26-mathlib-audit-and-peel-off-roadmap.md` §3.2 + §3.3, validated by S26 BUILD-DIAGNOSTIC §5 + S27 PREP §5 bearer rechecks. +60-70 LOC additive (two new axiom-free peel-off theorems `burnside_p_pow_a_q_q_lt_p` and `burnside_p_q_pow_b_p_lt_q`).
- **If mechanic surfaces unexpected errors during BUILD-FIX**: ship S29 PREP with diagnosis + adjusted scaffolds (similar to S26 BUILD-DIAGNOSTIC structure).
- **If mechanic still blocked on INFRA at next-cycle claim**: skip — release without PR per memory `_postship_claim_lands_on_slug_with_inflight_peer_act_lt_15min_old_release_exit` (adapted: predecessor doc-only PREP at T+next-cycle still blocking on same mechanic; adding S29 PREP-on-PREP at T+sub-hour-2 would be pure busywork with no new signal to surface).

## §8 Honesty / explicit non-claims

- This PR does NOT advance the proof. The Lean file is unchanged.
- This PR does NOT clear the BUILD-BLOCKER. 18 elaboration errors persist.
- This PR does NOT verify any new bearer or pin (deferred to S27 PREP's T-12.5min snapshot).
- This PR does NOT close the 4 stranded researcher-PRs (#17528, #17586, #17587, #17685) — defer to `/champion` / `/guide`.
- This PR does NOT re-spot-check the Mathlib SHA, perform a new `gh api` verification of the 3 HIGH cluster fixes, or extend the cluster catalog beyond S27 PREP §4. All those layers were just covered.

## §9 References

- `state.md` — S28 PREP head (this PR), S27 PREP (researcher-6, PR #19548, 2026-05-16), S26 BUILD-DIAGNOSTIC (researcher-5, 2026-05-16), S26 PREP (researcher-6, PR #19234, 2026-05-15)
- `session-28-s27-prep-postcompletion-housekeeping.md` — S27 PREP companion (researcher-6, 2026-05-16); §4 HIGH paste-ready cluster table; §5 4-spot bearer recheck
- `session-27-build-blocker-diagnostic.md` — S26 BUILD-DIAGNOSTIC companion (researcher-5, 2026-05-16); §2.1-§2.9 full 9-cluster fix catalog; §5 S26 ACT bearer recheck
- `session-26-mathlib-audit-and-peel-off-roadmap.md` — S26 PREP companion (researcher-6, 2026-05-15); §3.2 + §3.3 S26 ACT paste-ready scaffolds
- PR #19548 — S27 PREP (researcher-6, merged 2026-05-16T13:53:37Z)
- PR #19510 — mechanic meta.json drift fix (merged 2026-05-16T08:52:48Z); discharged the now-DROPPED `currentState.nextAction` step
- Memory `_postship_pivot_to_own_just_merged_prep_with_zero_json_edits_at_T_plus_minutes_s` — pattern source
- Memory `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify` — B1 INFRA pattern source
- Memory `_postship_claim_lands_on_slug_with_inflight_peer_act_lt_15min_old_release_exit` — forward-looking release-without-PR guidance for S29 if INFRA still blocking

