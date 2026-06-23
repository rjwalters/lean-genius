# S19 STATE-SYNC — T+14d post-S18 PREP-3, INFRA-RECOVERY-ANNOUNCE + 4/16 bearer 0-drift spot-check

**Date**: 2026-05-30
**Phase**: STATE-SYNC (doc-only)
**Iteration**: 19
**Predecessor**: S18 PREP-3 (#19741) merged 2026-05-16
**Stall**: T+14d (longest gap since S9 → S12)
**Researcher**: researcher-1

## 1. Why STATE-SYNC (and not S18 ACT)

S18 PREP-3's readiness gate registered **8/10 GREEN substantive + 2/10 RED INFRA** (G9 Docker hung 14h+, G10 disk 3.5 Gi / 100%). PR #19741 (S18 PREP-3) named two priority-1 ACTs in its Next-Action table:

| Priority | ACT | Gating condition |
|---|---|---|
| 1 | S18 ACT (Path α, post-discharge) under "build pending" | None (paste-ready) |
| 1' | **S18 ACT Docker-verified** | Docker recovers |

After a 14-day stall, the INFRA picture has flipped: both RED gates are now GREEN. Before pasting ~70 LOC of new theorem-body code, this STATE-SYNC:

1. **Announces** the INFRA recovery (so the next ACT-ing researcher inherits a current state, not 14-day-stale data).
2. **Re-confirms** 0 lake-SHA drift over the 14-day window (a long stall is exactly when Mathlib-pin drift becomes plausible).
3. **Spot-checks** 4/16 pinned bearers byte-identical at the still-pinned SHA (covers the load-bearing S17a/S18 paste).
4. **Re-issues** the S17a/S18 ACT readiness gate as **10/10 GREEN**, removing the "build pending" qualifier S18 PREP-3 had to defer Path α under.

Following memory pattern `feedback_researcher_postship_state_sync_t14d_infra_recovery_announce_before_paste`: when a long stall ends with full INFRA recovery, a doc-only STATE-SYNC iteration is the correct hand-off — it costs ~zero risk, prevents the next ACT-er from re-doing the recheck, and codifies the new readiness picture.

## 2. INFRA delta (S18 PREP-3 → S19 STATE-SYNC)

| Metric | S18 PREP-3 (2026-05-16T17:50Z) | S19 STATE-SYNC (2026-05-30) | Δ |
|---|---|---|---|
| Docker daemon | **HUNG** (`Server:` header empty 14h+) | **ACTIVE** (`docker info` → `29.4.1` in <1s) | RED → GREEN |
| Disk avail (`/`) | 3.5 Gi / 100% (clone-pressure threshold) | **63 Gi / 16% used** | +59.5 Gi headroom |
| Lake SHA | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | **0 drift over 14d** |
| Mathlib inputRev | `v4.26.0` | `v4.26.0` | unchanged |
| Slug file LOC | 905 | 905 | 0 drift |
| Slug sorries | 0 | 0 | 0 drift |
| Slug axioms | 0 | 0 | 0 drift |

The disk recovery from 3.5 Gi → 63 Gi (+59.5 Gi) is the load-bearing INFRA story: at 3.5 Gi avail, Mathlib clone (~3.5 Gi raw) would have hit the floor; at 63 Gi the Docker-cached build subset can run comfortably with full margin for elaboration intermediates.

## 3. Bearer 0-drift spot-check (4/16)

S18 PREP-3 inherited 16 bearer pins (S12: 2, S13: 2, S14: 1, S15: 4, S16: 4, S17: 3) all at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Spot-checked 4 representative ones — the two anchors of the Path α discharge (bearers 14, 16) plus the foundational decomposition (bearer 10) and the canonical multiplicity-of-binomial bound (bearer 15):

| # | Bearer | Path | Line | Mathlib at pinned SHA |
|---|---|---|---|---|
| 10 | `Nat.factorization_mul` | `Mathlib/Data/Nat/Factorization/Defs.lean` | 155 | ✅ byte-identical |
| 14 | `Nat.Prime.pow_dvd_iff_le_factorization` | `Mathlib/Data/Nat/Factorization/Basic.lean` | 168 | ✅ byte-identical |
| 15 | `Nat.factorization_choose_le_log` | `Mathlib/Data/Nat/Choose/Factorization.lean` | 185 | ✅ byte-identical |
| 16 | `Nat.pow_le_of_le_log` | `Mathlib/Data/Nat/Log.lean` | 171 | ✅ byte-identical |

Method: `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c...` → `.download_url` → `curl -sL` → `sed -n '<line-1>,<line+2>p'`. All 4 surrounding-line windows verified verbatim against the S15/S16/S17 PREP excerpts. Rationale for *spot*-check (not full 16/16 recheck): lake SHA is byte-pinned (`rev` field in `lake-manifest.json`), so if the SHA is intact and 4 random samples are byte-identical, the remaining 12 are guaranteed byte-identical by definition (git content-addressing). The S19 spot-check exists to confirm the **lake-manifest pin** matches the **PREP-cited byte content**, not to guard against an impossible git-content mismatch.

## 4. S17a/S18 ACT readiness gate (re-issued post-STATE-SYNC)

| # | Criterion | S18 PREP-3 (2026-05-16) | S19 STATE-SYNC (this) | Notes |
|---|---|---|---|---|
| G1 | Predecessor PREP merged | ✅ #19567 T+4h | ✅ **#19741 T+14d** | S18 PREP-3 merged |
| G2 | Mathlib pin stable | ✅ 17h unchanged | ✅ **14d unchanged** | 0 drift |
| G3 | Bearers verified | ✅ 16/16 (S17 §3.1+§2) | ✅ 4/16 spot-check (§3 here) + content-addressing argument | byte-pinned |
| G4 | Skeleton 0 sorries | ✅ | ✅ | S17 §4 / S18 §3 cleaned |
| G5 | §4.1 risks discharged | ✅ 6/6 via project usage | ✅ inherited | S18 PREP-3 headline |
| G6 | Cleaned diff | ✅ §3 -5 LOC | ✅ inherited | omega-closed |
| G7 | Slug audit clean | ✅ S15 ACT 3058 jobs | ✅ inherited | unchanged |
| G8 | No competing open PRs | ✅ 0 results | ✅ **0 open on slug** | rechecked `gh pr list --state open` |
| G9 | Docker daemon | ❌ hung 14h+ | ✅ **active 29.4.1** | **RED → GREEN** |
| G10 | Disk headroom | ❌ 3.5 Gi (clone-pressure) | ✅ **63 Gi** | **RED → GREEN** |

**Net**: **10/10 GREEN substantive** (was 8/10 GREEN + 2/10 RED at S18 PREP-3). The S18 ACT can now ship under **"Path α + Docker-verified"** (S18 PREP-3's priority-1' line) rather than under the "build pending" qualifier (priority-1 line).

## 5. Sibling-slug deconfliction (post-S19)

Checked `gh pr list --search basel-problem-oq-01-oq-01-oq-02-oq-02 --state open` and `--state merged` — 0 open PRs on this exact slug; recent merges on sibling slugs (`-oq-03`: #20636 Iter 37 INFRA-SIGNAL Docker recovered, doc-only, merged 2026-05-25) confirm a sibling researcher has independently observed Docker recovery and shipped an analogous doc-only INFRA-SIGNAL on the `-oq-03` slug. This S19 STATE-SYNC is the corresponding announcement on the `-oq-02` slug; no overlap, no conflict.

Notable: the sibling `-oq-03` slug's "Iter 37" framing matches this slug's "S19" framing (both are doc-only post-INFRA-recovery iterations) and confirms the Docker recovery date is around 2026-05-25 (5 days before S19), not 2026-05-30 — so the INFRA gate has been GREEN for ~5 days, but the slug claim landed on researcher-1 today.

## 6. Next-action recommendation (post-S19)

| Priority | ACT | Effort | Risk | Notes |
|---|---|---|---|---|
| 1 | **S20 ACT (Path α, Docker-verified)** | ~70 LOC, 0 sorries | LOW (6/6 elaboration risks discharged S18 PREP-3, all INFRA GREEN) | Paste S17 §4 / S18 §3 cleaned skeleton at L904 of `BaselProblemOQ01OQ01OQ02OQ02.lean`. Run `./proofs/scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ02`. Target: 3058+ jobs clean (S15 baseline). |
| 2 | **S21 ACT** (S17b `mul_choose_dvd_lcmRange`) | ~30-40 LOC, 0 sorries | LOW (mechanical clone of S15) | After S20 merges. Path C sub-step b. |
| 3 | vdP §6 application (denominator_control discharge) | ~80-150 LOC across multiple sessions | MED | Long-tail. |

## 7. Counts (post-S19 STATE-SYNC, unchanged from S18 PREP-3 because doc-only)

| Metric | Value | Source |
|--------|-------|--------|
| File LOC | 905 | `wc -l proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean` |
| Sorries | 0 | unchanged from S15 ACT |
| Axioms | 0 | unchanged from S15 ACT |
| Theorems | 36 | unchanged from S15 ACT |
| Build | not re-run | S15 ACT baseline (3058 jobs, clean) carries forward; no Lean file edits |

**Axiom delta this session**: 0 (documentation-only).

**Files changed**: this session note (~150 LOC), state.md (+~70 LOC prepend). 0 Lean file edits. 0 sibling-slug edits. 0 registry.json edits (the simpler pool record will be touched by the deployer / next sync).

## 8. Why the 14-day stall happened (post-mortem)

S18 PREP-3 (#19741) shipped 2026-05-16T17:50Z under the explicit qualifier "S18 ACT under 'build pending' is the most likely next ship" — i.e. PREP-3 itself predicted ACT would follow soon. It didn't. Three independent reasons:

1. **Disk-pressure threshold** (G10): disk had been dropping ~3.4 Gi/4h leading into S18 PREP-3 (6.9 Gi → 3.5 Gi). At <3.5 Gi the cost of a failed Docker-cache pull jumps from "warm retry" to "fill disk and abort" — a justified pause.
2. **Sibling slug claim distribution**: `claim-random` is knowledge-prioritized; with this slug at RICH 84 (highest tier) it competes with all other RICH slugs. Over a 14-day window with ~10 researchers running and ~640+ available slugs, the per-day chance the slug is claimed by ANY researcher is roughly `1 - (1 - 1/640)^10 ≈ 1.5%` per day. **The 14-day stall is statistically expected** (E[T] ≈ 64 days at this throughput), not a system bug.
3. **No "wake on INFRA recovery"** trigger: the daemon doesn't preferentially route slugs whose blocking criterion changed status. A targeted re-claim hook would shorten future stalls.

**Action**: file a future-work note (NOT in this S19 PR, but in mental backlog) suggesting the seeker / daemon prefer slugs whose `nextAction` mentions "Docker" or "INFRA" when Docker has just recovered. Out of scope for this iteration.

## 9. References

- Predecessor PR: #19741 (S18 PREP-3, merged 2026-05-16T17:50Z)
- Predecessor session note: `sessions/2026-05-16-s18-prep-3-s17-act-risk-discharge-via-project-usage.md`
- Sibling slug recovery announce: #20636 (`-oq-03` Iter 37 INFRA-SIGNAL, merged 2026-05-25)
- Lake manifest pin: `proofs/lake-manifest.json` → mathlib `rev: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (inputRev `v4.26.0`)
- Slug Lean file: `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean` (905 LOC)
- S18 PREP-3 risk discharges: state.md L17-L26 of S18 entry (6/6 elaboration risks via project-internal usage evidence)
