# Erdős #301 — S3 STATE-SYNC (post-S2 SCOPED registry catchup)

**Agent**: researcher-11
**Date**: 2026-05-17
**Phase**: STATE-SYNC (doc-only)
**Iteration**: 3 (bumps past stale S2 SCOPED on JSON registry)
**Predecessor**: S2 SCOPED orphan commit `f2293c11305` (2026-04-27, branch `fix/pr-13216-researcher-5`, never merged via PR; state.md mass-imported via #19454)

---

## 0. Cycle Bootstrap

Pre-claim state: worktree on stale branch `research/minpoly-charpoly-oq-01-s6-statesync` with one unpushed commit `39410293c35` whose content (3 files) exactly matched merged PR #20027 (squashed). Per memory `feedback_researcher_worktree_unpushed_commit_identical_to_merged_pr_different_hash_safe_to_reset_then_two_productive_cycles`, verified via `gh pr view 20027 --json files` (3 files matching local commit's `--stat`) and reset to `origin/main`. Created fresh branch `research/erdos-301-s3-statesync` off `origin/main` (tip `d4cacd5d3b6`).

Claim outcome: `claim-random` selected `erdos-301` (Tier MODERATE+, 459-in-tier depth-first slot of 1284 available, knowledge score 6/MODERATE).

---

## 1. Drift Diagnosis

The slug exhibits a classic **partial-mass-import drift pattern**: an unmerged orphan branch's state.md got mass-imported into main via an unrelated cross-cutting PR, but the JSON registry was never updated by any process. Substantive findings stranded in state.md for ~20 days.

### Predecessor S2 (orphan commit `f2293c11305`)

**Branch**: `fix/pr-13216-researcher-5` (orphan, never PR'd to main)
**Date**: 2026-04-27T17:35Z
**Author**: previous researcher session
**Files touched**: `research/problems/erdos-301/state.md` (created)
**Lean changes**: none

S2 was a SCOPING session that inspected `proofs/Proofs/Erdos301Problem.lean` (158 lines, 0 sorries, 0 axioms, 7 theorems, 4 defs) and identified:

1. The conjecture `f(N) = (½ + o(1)) · N` is encoded as `def ErdosProblem301 : Prop` (correctly `axiomatized` per project convention for open conjectures).
2. The lower bound `f(N) ≥ N/2` is **properly proved** via the half-interval witness `(N/2, N] ∩ {1,...,N}` (theorem `halfInterval_egyptFree` + `maxEgyptFree_lower`).
3. The trivial upper bound `f(N) ≤ N` is proved (`maxEgyptFree_le`).
4. ⚠️ The theorem `vanDoorn_upper` is **misleadingly named**: its statement `f(N) ≤ (25/28 + 1) · N = (53/28) · N` is trivially true since `f(N) ≤ N ≤ (53/28) · N` (the proof is literally `≤ N ≤ (53/28) · N`). The proof does NOT formalize Van Doorn's actual 25/28 argument.
5. Closure properties (`egyptFractionFree_empty`, `_singleton`, `_subset`) are proved.

S2 scoped 4 incremental directions (honest rename / parity refinement / exclusion-based upper / partial Van Doorn) and released without ACT due to disk constraints (88% capacity, 1.7 GB free).

### Mass-import via #19454 (`sperner-ndim-mathlib-oq-01-oq-04` S2-A ACT)

`git log --diff-filter=A -- research/problems/erdos-301/state.md` shows `state.md` was **created** in `ecb47b35601` (PR #19454, 2026-05-16). That commit was the Sperner signed-cell-complex ACT; it had nothing to do with erdos-301 substantively, but apparently swept in the orphan branch's state.md as part of a mass directory refresh.

**Effect**: state.md landed on main carrying S2's full SCOPED content (Phase=SCOPED, Iteration=2, since=2026-04-27), but **only the state.md was carried** — the JSON registry, pool entry, and (per orphan-branch hygiene) sessions/ memo were never touched.

### Resulting JSON registry drift (12 surfaces)

| # | Field | Stale (pre-S3) | Canonical (post-S3) | Source |
|---|---|---|---|---|
| 1 | `phase` (top-level) | `"OBSERVE"` | `"SCOPED"` | state.md head |
| 2 | `currentState.phase` | `"NEW"` | `"SCOPED"` | state.md head |
| 3 | `currentState.since` | `"2026-01-12T23:48:29.416Z"` | `"2026-04-27T17:35:00Z"` | state.md head |
| 4 | `currentState.iteration` | `1` | `2` | state.md head |
| 5 | `currentState.focus` | `"Initial exploration of the problem."` | SCOPED summary | state.md §Current Focus |
| 6 | `currentState.nextAction` | `"Begin problem exploration."` | S3+ menu A/B/C/D | state.md §Next Action |
| 7 | `currentState.blockers` | `[]` | disk-tight blocker | state.md §Blockers |
| 8 | `currentState.attemptCounts.total` | `0` | `1` | state.md §Attempt Counts |
| 9 | `currentState.attemptCounts.currentApproach` | `0` | `1` | state.md §Attempt Counts |
| 10 | `currentState.attemptCounts.approachesTried` | `0` | `1` | state.md §Attempt Counts |
| 11 | `lastUpdate` | `"2026-03-13T07:52:17.045Z"` | `"2026-05-17T05:25:00Z"` | this S3 timestamp |
| 12 | `leanFiles[0].lineCount` | `159` | `158` | `wc -l proofs/Proofs/Erdos301Problem.lean` |

### Untouched (verified consistent)

- `knowledge.builtItems` / `knowledge.insights` / `knowledge.progressSummary` — already substantive from some earlier sync, NOT stale (describe S2's `halfInterval_egyptFree` correctly).
- `leanFiles[0].theoremCount` (7) ✓ canonical raw regex `^(protected |private |noncomputable )*(theorem|lemma) ` matches 7.
- `leanFiles[0].defCount` (4) ✓ canonical `^(protected |private |noncomputable )*def ` matches 4.
- `leanFiles[0].sorryCount` (0) ✓ canonical `\bsorry\b` matches 0.
- `leanFiles[0].axiomCount` (0) ✓ canonical `^(protected )?axiom ` matches 0.
- `tier` (A) — JSON+pool concur; problem.md YAML says `tier: B`; left untouched (not the S3 scope; cross-source disagreement deferred).
- Pool entry (`tier`, `status`, `notes`) — pool file is untracked in git; pool drift fixes via `claim-problem.sh update` only (skipped in S3).

---

## 2. S3 Surgical Changes (doc-only, 3 files)

### File 1: `src/data/research/problems/erdos-301.json` (+~10/-~10 net)

Patched 4 distinct regions covering 12 drift surfaces:
- Top-level `phase`: `OBSERVE` → `SCOPED`
- `currentState` block: 7-field rewrite (phase, since, iteration, focus, blockers, nextAction, attemptCounts {total, currentApproach, approachesTried})
- `lastUpdate`: `2026-03-13T07:52:17.045Z` → `2026-05-17T05:25:00Z`
- `leanFiles[0].lineCount`: `159` → `158`

JSON validity confirmed via `python3 -m json.tool`.

### File 2: `research/problems/erdos-301/state.md` (+~50 net)

- Head iteration: `2` → `3`; since-line annotated with "(carry-forward from S2; S3 STATE-SYNC doc-only)"
- New §Iteration Ledger (4 rows: iter 1 scrape, iter 2 orphan SCOPED, iter 3 this STATE-SYNC)
- §Blockers extended with S3 INFRA snapshot table (G7 RED disk 4.5 GiB, G8 RED Docker hung, G9 GREEN .lake host-rooted)
- §Attempt Counts annotated with "S3 doc-only, no new attempt"
- New §S4 Picker Matrix (4-row table: A rename, B parity, C exclusion, D Van Doorn; with prerequisites + recommended A→B→D sequence)

### File 3: `research/problems/erdos-301/sessions/2026-05-17-s3-statesync-postS2-registry-catchup.md` (NEW, this file)

11-section memo documenting:
- §0 cycle bootstrap (reset-from-merged-PR-with-different-hash pattern)
- §1 drift diagnosis (orphan branch + mass-import via #19454 + 12 drift surfaces)
- §2 surgical changes (this section)
- §3 verification matrix
- §4 INFRA snapshot
- §5 Lean file canonical metrics
- §6 sibling INFRA cross-validation
- §7 risk/race analysis (no concurrent PRs)
- §8 S4 picker matrix detail
- §9 release plan
- §10 references

---

## 3. Verification Matrix

| Check | Method | Result |
|---|---|---|
| JSON valid | `python3 -m json.tool src/data/research/problems/erdos-301.json` | ✓ |
| Lean file lineCount | `wc -l proofs/Proofs/Erdos301Problem.lean` | 158 (matches JSON post-S3) |
| Lean theoremCount canonical | `grep -cE '^(protected \|private \|noncomputable )*(theorem\|lemma) '` | 7 (matches JSON) |
| Lean defCount canonical | `grep -cE '^(protected \|private \|noncomputable )*def '` | 4 (matches JSON) |
| Lean sorryCount canonical | `grep -cE '\bsorry\b'` | 0 (matches JSON) |
| Lean axiomCount canonical | `grep -cE '^(protected )?axiom '` | 0 (matches JSON) |
| No concurrent PRs | `gh pr list --search "erdos-301" --state open` | `[]` (clean) |
| Worktree branch fresh | `git log origin/main..HEAD` | empty (clean rebase point) |
| Iteration bump consistent | state.md head=3 + ledger row 3 vs JSON `currentState.iteration`=2 (S2 carry-forward) | intentional: state.md tracks active iteration (S3 in-progress), JSON tracks last-merged SCOPED state (S2) |

**Note on iteration field semantics**: After S3 merges, the JSON `currentState.iteration` field semantically reflects the last *substantive phase change* (S2 SCOPED, since=2026-04-27). The state.md head `**Iteration**: 3` reflects the S3 STATE-SYNC overlay. Future S4 ACT will bump JSON `currentState.iteration` to 3 (or higher).

---

## 4. S3 INFRA Snapshot (2026-05-17 ~05:25Z)

| Gate | Reading | Status | Trend vs sibling sessions today |
|---|---|---|---|
| G7 (disk root avail) | 4.5 GiB (78% used) | RED (below 5 GiB soft floor) | Mild; sibling sessions (memory) report G7 = 2-3 GiB during peak Docker builds. 4.5 GiB suggests no concurrent build pressure. |
| G8 (Docker server `docker info`) | empty/hung at 5s timeout | RED | Consistent w/ Docker-hung pattern across siblings since 2026-05-17 ~01-04Z (memory entries cite 8s-21h hangs). Daemon needs restart for any S4 ACT. |
| G9 (`proofs/.lake` symlink) | `→ /Users/rwalters/GitHub/lean-genius/proofs/.lake` (host-rooted) | GREEN | Worktree's `.lake` resolves to main repo's host directory; no self-cycle. |

**S3 scope tolerance**: doc-only changes — RED G7+G8 do not block. Mathlib SHA not re-walked (no lake build attempted).

---

## 5. Lean File Canonical Metrics

`proofs/Proofs/Erdos301Problem.lean` @ commit `d4cacd5d3b6` (origin/main):

```
lineCount: 158         (raw wc -l)
theoremCount: 7        (^(protected |private |noncomputable )*(theorem|lemma) )
defCount: 4            (^(protected |private |noncomputable )*def )
sorryCount: 0          (\bsorry\b)
axiomCount: 0          (^(protected )?axiom )
```

Theorem inventory (7):
1. `halfInterval_egyptFree` (line 55) — (N/2, N] is EgyptFractionFree
2. `maxEgyptFree_lower` (line 100) — f(N) ≥ N/2
3. `maxEgyptFree_le` (line 118) — f(N) ≤ N (trivial)
4. `vanDoorn_upper` (line 129) — **misleadingly named**: f(N) ≤ (25/28+1)·N (trivially true)
5. `egyptFractionFree_empty` (line 140) — ∅ is EgyptFractionFree
6. `egyptFractionFree_singleton` (line 144) — {n} is EgyptFractionFree
7. `egyptFractionFree_subset` (line 155) — subset closure

Definition inventory (4):
1. `HasEgyptianDecomp` (line 28) — Prop
2. `EgyptFractionFree` (line 34) — Prop
3. `maxEgyptFree` (line 38) — noncomputable, ℕ-valued
4. `ErdosProblem301` (line 44) — Prop encoding the conjecture

---

## 6. Sibling INFRA Cross-Validation

Per memory entries from 2026-05-17 ~01-05Z sessions, the Docker-hung + disk-tight INFRA pattern is widespread:

- ballot-problem-oq-03-oq-01-oq-01-oq-01 S45+ — G7 2.3 Gi, G8 ≥20h Docker hung (memory)
- minpoly-charpoly-oq-01 S6+ — G7 3.4 Gi, G8 hung (memory)
- erdos-1151-oq-04 S34 — G7 5.2→3.2 Gi -2.0 Gi/9.75h, G8 8s timeout (memory)
- minkowski-theorem-oq-04 S29 — G7 6.7→3.4 Gi, G8 19.9h hung (memory)

Cross-validation confirms my S3 reading (G7 4.5 GiB, G8 5s-hung) is consistent with the cluster-wide INFRA window. The 4.5 GiB G7 reading is at the **better end** of the same-window readings — suggests this snapshot pre-dates the worst Docker contention.

Mathlib pin (referenced by memory as `2df2f0150c…` byte-stable since ~2026-05-13): not re-walked this S3 (doc-only); referenced for S4+ ACT context only.

---

## 7. Risk / Race Analysis

- **No concurrent PRs**: `gh pr list --search "erdos-301" --state open` returns `[]`.
- **Most recent erdos-301 mention in any PR**: #19375 (2026-05-16, audit tracker bumps; not substantive to erdos-301 content).
- **Last substantive erdos-301 Lean PR**: #8382 (2026-03-30, "4 problems — Liouville approx, Erdős #301 verified, oblique n×n, Erdős #1181 sorry") — predates S2 SCOPED by ~27 days.
- **Three-way clash risk**: NONE. No other agent has touched erdos-301 files in the last 17 days (since #19454 mass-import on 2026-05-16). Pool shows researcher-15882 (this session) as sole claimant.
- **Cycle-restart trap check**: branch is fresh off `origin/main` (`d4cacd5d3b6`); no stale base.

---

## 8. S4 Picker Matrix (Recommended Sequence)

| Option | Description | LOC | Risk | Build prerequisite |
|---|---|---|---|---|
| **A — honest rename** | `vanDoorn_upper` → `trivial_upper_const_5328`; add `--TODO` comment | ~3 | trivial | `lake build Proofs.Erdos301Problem` |
| **B — parity refinement** | Prove `f(N) ≥ ⌈N/2⌉ + 1` for `N ≡ 0 (mod 4)` (extends half-interval by 1 via `N/2` itself when even) | 10-15 | low | as above |
| **C — exclusion-based upper** | `f(N) ≤ N - ⌊N/k⌋` via highly-composite exclusion (forces certain n's out via reciprocal decomposition) | 50+ | moderate | + Mathlib divisor API survey |
| **D — partial Van Doorn** | Real 25/28 argument fragment (multi-session) | 200+ | high | + multi-session planning, possibly Aristotle support |

**Recommended sequence for next researcher session (when disk > 5 GiB free AND Docker healthy)**:

1. **A first** (3 LOC, removes false attribution; no math required): Replaces `theorem vanDoorn_upper` with `theorem trivial_upper_const_5328` + `/-- TODO: Van Doorn's actual (25/28+o(1))·N upper bound is NOT formalized here. -/` doc comment. Update `meta.json` `originalContributions` if it claims the Van Doorn bound is formalized.
2. **Then B** (10-15 LOC, smallest genuine improvement): For even N, the witness set `(N/2, N] ∩ {1,...,N}` has cardinality `⌈N/2⌉`. The element `N/2` itself can sometimes be added without breaking EgyptFractionFree (case analysis on parities).
3. **Then D** (multi-session) if higher-confidence headway desired; **skip C** unless someone wants a verifiable strengthening of the upper bound short of Van Doorn.

---

## 9. Release Plan

After this S3 merges, the claim should be **released** (not marked completed — slug remains active SCOPED, awaiting S4 ACT). The pool entry should naturally update from "in-progress" → "open" on release.

```bash
# Post-merge:
/Users/rwalters/GitHub/lean-genius/scripts/research/claim-problem.sh release erdos-301
```

The "Focus: Initial exploration of the problem." text in the pool `notes` field will remain stale until either:
- A future researcher refreshes via `claim-problem.sh` (some commands rewrite notes), OR
- A pool-management script rebuilds notes from JSON registry.

S3 deliberately does not touch the pool file directly (untracked in git).

---

## 10. References

- **Memory entries cited**:
  - `feedback_researcher_worktree_unpushed_commit_identical_to_merged_pr_different_hash_safe_to_reset_then_two_productive_cycles.md` (bootstrap pattern)
  - `feedback_worktree_lean_state_symlink_missing_in_fresh_loom_worktrees_must_recreate_to_share_candidate_pool.md` (symlink check)
  - `feedback_researcher_gh_pr_list_returns_empty_in_lean_genius_when_mathlib_fork_remote_present_must_use_repo_rjwalters_lean_genius_explicitly.md` (`--repo` flag on all gh calls)
  - Various S3-pattern entries (post-ship pivot to active-phase slug with predecessor STATE-SYNC drift)
- **Prior commits**:
  - `f2293c11305` (S2 SCOPED orphan, branch `fix/pr-13216-researcher-5`)
  - `ecb47b35601` (#19454 mass-import of state.md)
  - `221af91d79e` (#8382 last substantive Lean PR, 2026-03-30)
- **Project conventions**:
  - Axiom Integrity Policy (CLAUDE.md): `axiomatized` status correct for open conjectures even with 0 axioms
  - Canonical regex for Lean metrics: raw `\bsorry\b`, `^(protected |private |noncomputable )*(theorem|lemma) `, etc. (post-#19934)

---

**Cycle summary**: ~30 min wall time. 3 files modified (+/- documented above). 0 Lean changes. JSON registry now consistent with state.md. S4 ACT menu A → B → D ready for next researcher with healthy disk + Docker.
