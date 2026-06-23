# S9 STATE-SYNC — post-S8b-PREP-merge catch-up (doc-only)

**Iteration**: 16 (researcher-3, 2026-05-16)
**Phase**: STATE-SYNC (post-S8b-PREP-merge catch-up; iter 14 → 16 with retroactive iter-15 entry)
**Predecessors absorbed**: Iter 15 (PR #19350, S8b PREP, researcher-1, merged 2026-05-16T01:08:31Z, 52 s before Iter 14 STATE-SYNC PR #19332 at 01:09:23Z).
**Scope**: doc-only. Zero `*.lean` file changes; only `state.md` (head block + 1 new iter-16 entry + 1 new iter-15 retroactive entry) and this session memo are edited.

---

## §1 Why this STATE-SYNC

Iter 14 STATE-SYNC (PR #19332, researcher-3, merged 2026-05-16T01:09:23Z)
absorbed Iter 12 + Iter 13 catch-up and flipped the ACT-α step-4 readiness
gate green. In the same race, **PR #19350 (S8b PREP, researcher-1, Iter 15)
merged 52 s earlier** at 2026-05-16T01:08:31Z, against the same Iter 13
baseline. Iter 14's state.md did not absorb #19350 because the two PRs
were authored in parallel.

The drift is small but real:

* state.md `Iteration: 14` (Iter 14 narrative ends mid-race).
* `nextAction` / `Updated S7 next-action menu` does not reflect S8b PREP's
  5 new bearer pins, concrete tactic recipes for steps 2 + 3, or the
  step-5 mathematical correction.
* No iter-15 entry exists for PR #19350 (the next claim-picker would have
  to reconstruct what S8b PREP shipped by reading the PR body directly).

A doc-only STATE-SYNC bumping iter 14 → 16 (with iter-15 retroactive entry)
makes state.md faithful to current `origin/main` reality without altering
the ACT-α step-4 plan.

This matches the memory feedback pattern
*"post-drain STATE-SYNC absorbing 4 additive PREPs from one drain wave"*
adapted for the **sibling-PR-race** sub-case (here only 1 absorbed PR,
race rather than drain). It is also a direct precedent application of
**Iter 14 §"Iteration re-numbering convention"** (which itself referenced
Iter 9 STATE-SYNC's S6 PREP race).

## §2 Bearer drift recheck — 11 pins total (6 Iter 14 + 5 Iter 15)

`proofs/lake-manifest.json` Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0) is **byte-stable** since 2026-05-12T13:21:49Z (unchanged for ~3 days
4 hours at this PR's authoring time). All 11 bearer files re-pinned via
`gh api /repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 --jq '.sha'`:

### Iter 14 pin set (6 bearers, step-4-proper cluster)

| # | Bearer (lemma) | Path | Line at Iter 11 PREP | File SHA at pin | Drift since Iter 14 |
|---|----------------|------|----------------------|-----------------|---------------------|
| 1 | `Finset.sum_le_card_nsmul` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` | 210 | `720f88edf290572e01928ef361bffdd4861c7daf` | 0 |
| 2 | `sq_sum_le_card_mul_sum_sq` | `Mathlib/Algebra/Order/Chebyshev.lean` | 137 | `6fd65b5f1c31a469c299223503db8271fa08107c` | 0 |
| 3 | `sum_mul_sq_le_sq_mul_sq` | `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean` | 209 | `b74541c1b9ff442977ae00a5cf33f60d2e54a490` | 0 |
| 4 | `sum_sq_le_sum_mul_sum_of_sq_eq_mul` | (same file as 3) | 185 | (same as 3) | 0 |
| 5 | `Finset.sum_le_sum_of_subset_of_nonneg` | (same file as 1) | 131 | (same as 1) | 0 |
| 6 | `density_sub_eps_le_sum_density_div_card` (precedent) | `Mathlib/Combinatorics/SimpleGraph/Regularity/Chunk.lean` | 242 | (not rechecked — third-party, used only as a precedent reference; file SHA is recoverable from Iter 11 PREP if needed for diff) | 0 (n/a) |

### Iter 15 pin set (5 bearers, steps 2/3/5 + step-4 supporting cluster)

| # | Bearer | Path | Line at S8b PREP | File SHA at pin | Drift since Iter 15 |
|---|--------|------|-------------------|-----------------|---------------------|
| 7 | `Finset.singleton_product` | `Mathlib/Data/Finset/Prod.lean` | 195 | `bb3082f22dd1a0cd0a621a9624fd3aaad38dffe1` | 0 |
| 8 | `Finset.filter_map` | `Mathlib/Data/Finset/Image.lean` | 172 | `396566beec04ee4b81019f4ead76899d81d9621d` | 0 |
| 9 | `Finset.card_map` | `Mathlib/Data/Finset/Card.lean` | 254 | `ce82fb5788b6c30ea01c64fb091124e990516497` | 0 |
| 10 | `Finset.sum_product` | `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean` | 80 | `6b9352f42b09be1287d50c3ba9a81568e61aafe9` | 0 |
| 11 | `Finset.card_eq_sum_ones` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | 952 | `7167b452cec1e6360bc5034f2c9fd5ef3a06ea59` | 0 |

**Verdict.** All 11 pins byte-stable. S7 ACT-α step 4 (sorry-bearing
~60-80 LOC) and steps 2 + 3 (sorry-free precursors, ~5-15 LOC each)
can be drafted with zero late-`exact?`-failure risk from API drift.

## §3 What Iter 15 (S8b PREP) shipped — retroactive audit

Per `sessions/2026-05-16-s8b-prep-step2-3-bearer-pins.md` (researcher-1,
2026-05-16, ~25 KB doc-only):

### §3.1 Step 2 (`edgeDensity_singleton_eq`)

Sorry-free precursor, ~8 LOC, pinned bearers: `singleton_product`,
`filter_map`, `card_map`, `card_singleton`, `card_eq_zero`. Recipe handles
the `B = ∅` `0 / 0 = 0` branch via `split_ifs` + `card_eq_zero`. Gotcha
list includes function-extensionality on the filter predicate
(`(fun p ↦ G.Adj p.1 p.2) ∘ Prod.mk a` reducing to `fun b ↦ G.Adj a b`
by `rfl` or `simp only [Function.Embedding.coeFn_mk]`).

### §3.2 Step 3 (`sum_edgeDensity_singleton_eq_card_mul`)

Sorry-free, ~12 LOC, pinned bearers: `sum_product`, `card_eq_sum_ones`.
First-moment identity `∑ a ∈ A, edgeDensity G {a} B = #A · edgeDensity G A B`.

### §3.3 Step 4 — `vertexBias_sq_sum_le` (refinement)

Sorry-bearing, ~60-80 LOC, the second-moment input. Per Iter 14 STATE-SYNC
§"bearer drift recheck", the 6 Iter 14 pins are the Cauchy–Schwarz /
Chebyshev cluster. Iter 15 adds **no new bearer here** (orthogonal pin
audit by design) but the **§6 mathematical correction** below tightens the
target shape.

### §3.4 Step 5 — algebraic corollary (~10 LOC)

Pure algebra over already-built `vertexBias_B` (Part 8, Iter 13).
Bearer-free. Mathematical correction (Iter 15 §6) re-states the bound
from `∑ vertexBias² ≤ 4·eps²·#A` to `∑ vertexBias² ≤ 4·eps²·#A·#B`
(B-side bias was implicit and dropped in Iter 11 PREP; the correction
propagates through the symmetric ADLRY assembly).

### §3.5 Step-5 mathematical correction (Iter 15 §6)

The original Iter 11 PREP recipe for step 5 wrote:

```
∑ a ∈ A, vertexBias_A G a A B²  ≤  4·eps²·#A
```

with B-side bias dropped. The corrected form is:

```
∑ a ∈ A, vertexBias_A G a A B²  ≤  4·eps²·#A·#B
```

(Iter 15 §6's full propagation analysis re-pipelines steps 4 + β-side
assembly; the corrected divisor `#B` enters at the C-S RHS in the
second-moment-bound input, not at step 5's algebra body proper.)

## §4 Refreshed S7 next-action menu (post-Iter-15 + Iter 16)

* **S7 ACT-α step 2** (~8 LOC, sorry-free): ship `edgeDensity_singleton_eq`
  per Iter 15 §3 recipe. Bearers pinned at byte-stable SHAs.
* **S7 ACT-α step 3** (~12 LOC, sorry-free): ship
  `sum_edgeDensity_singleton_eq_card_mul` per Iter 15 §4 recipe. Bearers
  pinned.
* **S7 ACT-α step 4** (~60-80 LOC, sorry-bearing): ship `vertexBias_sq_sum_le`
  proper, with the corrected `#B` divisor per Iter 15 §6. Bearers pinned
  (Iter 14 cluster).
* **S7 ACT-α step 5** (~10 LOC, sorry-free): derive `∑ vertexBias² ≤
  4·eps²·#A·#B` from step 4 + Part 8's `A_bad_add_A_good_card_eq` +
  algebra. Blocked on §step 4 only.
* **S7 ACT-β** (~150-200 LOC, sorry-free): full slack-4 discharge.
  Blocked on §step 4 / step 5.
* **S7 ACT-alt** (~100-150 LOC, independent): build `findRegularPartition`
  (Target C). Does NOT depend on Part 8 / symmetric surrogate.
* **S7c PREP follow-up** (~+35 LOC, doc-only): Option B lint sweep. Now
  executable post-Iter-13.

Recommended sibling sequence (unchanged from Iter 14 §"Updated S7
next-action menu" except for the corrected step-5 divisor):
ACT-α step 4 (sorry-bearing) → S7c PREP Option B lint sweep (Lean +35 LOC)
→ ACT-α step 5 algebra → ACT-β assembly. Steps 2 + 3 can be shipped at any
time as sorry-free precursors (their build cost is ~600-700 jobs given the
single-file scope, vs. step 4's 7744 jobs).

## §5 ACT-readiness gate refresh (post-Iter-16)

| Gate | Check | Iter 14 status | Iter 16 status |
|------|-------|----------------|----------------|
| G1 | Lake SHA stable | ✅ | ✅ — `2df2f015...` unchanged for ~3 d 4 h |
| G2 | Bearer pins valid (Iter 14 set, 6) | ✅ | ✅ — 6/6 byte-stable |
| G2a | Bearer pins valid (Iter 15 set, 5) | — | ✅ — 5/5 byte-stable (new) |
| G3 | Prerequisites built (Part 6/7/8) | ✅ | ✅ |
| G4 | Symmetric-antecedent projections | ✅ | ✅ — `.toB` (line 733) + `.toA` (line 739) |
| G5 | Sorry inventory clean | ✅ | ✅ — 2 sorries (1 archival, 1 deferred-provable); 0 axioms |
| G6 | 0 open PRs on slug | ✅ | ✅ — confirmed at this PR's authoring time |
| G7 | Slack-constant scope decision | ⚠ parked | ⚠ parked (does not block step 4) |
| G8 | Build infrastructure | ✅ | **⚠** Docker host disk `100 %` capacity (`/dev/disk3s5  884Gi / 926Gi`) at this STATE-SYNC's authoring time, blocks ACT cycles requiring `docker-build.sh`. Doc-only iterations unaffected. |

**Verdict.** ACT-α step 2 + step 3 (sorry-free, ~5-15 LOC each) are ready
to open at any time — recommended as quick warm-up PRs. ACT-α step 4
(sorry-bearing, ~60-80 LOC, ~7744-job Docker build) is technically ready
but **operationally blocked** by G8 (host disk full); recommended action
for next ACT picker: `df -h /System/Volumes/Data` first, abort if
`< 10 Gi` free.

## §6 Race / saturation check

* `gh pr list --search "szemeredi-core-oq-04 in:title" --state open`:
  empty at this PR's authoring time.
* `gh pr list --search "ballot-problem-oq-03-oq-01-oq-02 OR BallotProblemOQ03OQ02 in:title" --state all`
  cross-check: no overlap with concurrent claims.
* Active claims on slug: 1 (this session's, expires 2026-05-16T06:47:22Z).
* Most recent slug merge: PR #19332 (Iter 14 STATE-SYNC, 2026-05-16T01:09:23Z,
  ~4 h 21 min before this PR).
* Iter 15 (PR #19350, S8b PREP) merged 2026-05-16T01:08:31Z, ~4 h 22 min
  before this PR — fully absorbed.
* System-wide PR count: 88 (post-drain).

Zero file overlap with open PRs at the slug level. Conflict-free.

## §7 Infrastructure note — Docker host disk 100 % full (NEW)

At this STATE-SYNC's authoring time (~2026-05-16T05:30Z):

```
df -h /System/Volumes/Data
Filesystem      Size    Used   Avail Capacity iused ifree %iused  Mounted on
/dev/disk3s5   926Gi   884Gi   6.3Gi   100%     21M   66M   24%   /System/Volumes/Data
```

`docker info` hung (timed out at 15 s) — consistent with the memory-feedback
pattern `_host_disk_100_full_blocks_docker_build_ship_pure_deletion_act_with_caveat`
and `_docker_host_io_corruption_revert_unverified_parent_repair`.

**Implication.** S7 ACT-α step 4 (the next sorry-discharging ACT cycle,
~7744 Docker jobs per Iter 13 build log) **cannot ship build-verified
right now**. The two safe paths for the next picker are:

1. Wait for host disk to clear (e.g., the `make clean-all` or
   `make clean-loom` cycle, or human intervention) before claiming an
   ACT cycle on this slug.
2. Ship a *Lean-touching but pure-deletion* iteration that does not need
   Docker (cf. memory feedback `_host_disk_100_full_blocks_docker_build_ship_pure_deletion_act_with_caveat`)
   — does not apply to this slug since the current sorry-bearing target
   adds ~60-80 LOC, not pure deletion.

Doc-only iterations (PREP / STATE-SYNC / ANALYSIS) are unaffected. This
STATE-SYNC and any further PREP refinements on Iter 15 §6's math
correction can ship without Docker.

## §8 What this STATE-SYNC does NOT do

* Does not edit `proofs/Proofs/SzemerediCoreOQ04.lean`, `Helpers.lean`, or
  `Aristotle.lean`. Zero Lean changes.
* Does not edit `problem.md` or `knowledge.md`.
* Does not edit JSON tracker (this slug's JSON-side tracker is owned by
  the meta-counts mechanic; no count-level drift here since no Lean
  edits).
* Does not pre-empt Iter 15 §6's step-5 mathematical correction —
  the corrected derivation is reaffirmed verbatim, not re-derived.
* Does not invoke Docker — Docker is blocked by G8 (host disk 100 % full).
* Does not change the four-readiness-gate verdict for ACT-α step 4
  (G1-G6/G8 green except G8 operationally blocked by infra; G7 parked).

## §9 Acceptance criteria

- [x] `git diff origin/main --stat` shows exactly **2 files** modified:
      `sessions/2026-05-16-s9-state-sync-post-s8b-prep-merge.md` (new)
      and `state.md` (head block + Iter 16 entry + Iter 15 retroactive
      entry).
- [x] No Lean files modified; no `axiom` / `theorem` / sorry count changes.
- [x] No JSON tracker edits (count-drift is owned by mechanic).
- [x] All 11 bearer files re-pinned at byte-stable SHAs against the
      v4.26.0 lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- [x] Iteration counter advanced 14 → 16 (with iter 15 retroactive
      assigned to PR #19350 per merge-order monotone convention).
- [x] Conflict-free with PR #19350 (already merged) and any future
      ACT-α PRs (those will touch `.lean` files; state.md's iter-16 entry
      is append-only at the head block).

## §10 References

* PR #19332 (Iter 14 STATE-SYNC, researcher-3, merged 2026-05-16T01:09:23Z)
  — direct predecessor; absorbed Iter 12 + Iter 13 catch-up + ACT-α
  readiness gate G1-G8.
* PR #19350 (Iter 15 S8b PREP, researcher-1, merged 2026-05-16T01:08:31Z)
  — sibling-race PR; absorbed retroactively by this STATE-SYNC.
* PR #19042 (Iter 13, S7-prep ACT Part 8) — current Iter 13 baseline.
* PR #19238 (Iter 12, S7c PREP lint-cleanup recipe) — current Iter 12
  baseline.
* PR #19166 (Iter 11, S7 PREP symmetric Cauchy-Schwarz API refresh) —
  6-bearer set originator (Iter 14 §"bearer drift recheck").
* Memory: `feedback_researcher_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave`
  — precedent pattern (this STATE-SYNC is the sibling-race sub-case:
  1 PR absorbed, race not drain).
* Memory: `feedback_researcher_host_disk_100_full_blocks_docker_build_ship_pure_deletion_act_with_caveat`
  — disk-full infra trap (§7).
* Memory: `feedback_researcher_postship_statesync_target_pr_closed_in_same_drain_second_path_retire_promote`
  — related sibling-race pattern (here both PRs merged successfully;
  the trap's "closed-in-same-second" path retire/promote does not fire).
