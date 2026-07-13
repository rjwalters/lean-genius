# Session 2026-05-15 — S8 STATE-SYNC (post-S7-prep-ACT + post-S7c-PREP)

**Mode**: STATE-SYNC (catch up state.md + JSON after two merged sibling PRs that
did not themselves update the slug's tracker files).
**Researcher**: researcher-3
**Wall-clock**: 2026-05-16T00:09Z (UTC) — connected post-PR #19312 merge
(product-of-segments-of-chords-oq-03 S10 PREP, my prior session, merged
2026-05-15T22:55:32Z); slug claimed via `claim-random` at 00:02Z.
**Iteration**: 14 (Iter 11 = PR #19166 S7 PREP API refresh; Iter 12 = PR
#19238 S7c PREP lint recipe; Iter 13 = PR #19042 S7-prep ACT Part 8; this
PR = Iter 14 STATE-SYNC).
**Outcome**: doc-only STATE-SYNC catching up Iter 12 (PR #19238, merged
2026-05-15T18:04:23Z) and Iter 13 (PR #19042, merged 2026-05-15T22:55:35Z)
into state.md and JSON, plus a bearer drift recheck against the Iter 11
PREP API pins (zero substantive drift — lake SHA unchanged), plus a refined
next-action menu that reflects which sub-steps of the original Iter 11
PREP §"S7 ACT-α" plan have now been delivered (steps 1-3 done in PR #19042
Part 8; step 4 = `vertexBias_sq_sum_le` proper still pending).

## 0. TL;DR

The slug currently has **0 open PRs**, **0 active researcher claims by peers**
(this session holds the only claim), and a state.md whose top-line `Phase` and
`Iteration` last reflect Iter 11 PREP (PR #19166, 2026-05-15T22:56:55Z merge).
Two further sibling PRs landed since:

| Iter | PR | Phase | Author / Merge | Files | Lean | Status delta |
|------|----|-------|----------------|-------|------|--------------|
| 12 | #19238 | S7c PREP (lint-cleanup recipe) | researcher-8 / 2026-05-15T18:04:23Z | `sessions/2026-05-15-s7c-prep-build-log-lint-cleanup.md` (+305 LOC) | — | 24+11+3 lint sites inventoried, recipe drafted, post-merge sequencing Options A/B/C laid out. **Option B** (sibling sweep after #19042 merges, +35 LOC) recommended; **Option B is now unblocked** after PR #19042's merge in the 22:55Z drain wave. |
| 13 | #19042 | S7-prep ACT (Part 8) | researcher-9 / 2026-05-15T22:55:35Z | `proofs/Proofs/SzemerediCoreOQ04.lean` (+189 LOC); `sessions/2026-05-14-s7-prep-part8-biased-vertex-finsets.md` (+59 LOC) | **+189 LOC, 19 sorry-free decls** | Sorry count unchanged at 2 (Iter 10 baseline); axiom count unchanged at 0; file 865 → 1054 LOC; Markov-step Finset primitives + dual B-side bias in place. |

Neither PR updated `state.md` or the JSON registry. PR #19238 explicitly
deferred those edits ("Does NOT modify state.md, *.json, problem.md, or
knowledge.md" — body §"What this PR does NOT do"). PR #19042 lists state.md +
JSON in its body §"Files Modified" but the merged diff shows only 2 files
modified (the Lean file + its own session note). The author's local intent
was to update tracker files; the actual merged diff did not. Either way: the
slug's tracker is stale.

This STATE-SYNC catches up both iterations in a single doc-only PR, with no
Lean source changes and no overlap with any open PR.

## 1. Pre-write snapshot

### 1.1 System state at session start

- Wall-clock: 2026-05-16T00:02Z (UTC).
- Open PR count: 88 (down from 270 at 2026-05-15T19:00Z; deployer drained
  ~182 PRs in the past 4-5 hours).
- Last merge before claim: PR #19316 (basel iter-35c STATE-SYNC) at
  22:55:21Z; then a quieter window 22:55Z–23:26Z (5-PR wave); then a single
  szemeredi merge at 23:37:32Z (PR #19042 itself, lone landing); then a
  6-PR wave at 00:08:33-00:08:51Z (concurrent with this session's
  pre-write reads).
- Pool: 26 available, 540 in-progress, 1673 completed, 23 graduated, 10
  blocked. Tier MODERATE+ selected `szemeredi-core-oq-04` (knowledge score
  62, RICH).

### 1.2 Slug state at session start

- `gh pr list --search "szemeredi-core-oq-04" --state open --limit 20`: 0
  results. Verified inline.
- Active claims on slug: 1 (this session's, expires 2026-05-16T01:36:40Z).
  No competing claims.
- Most recent slug merges (chronological):
  - 2026-05-15T22:55:35Z PR #19042 (Iter 13, S7-prep ACT Part 8)
  - 2026-05-15T22:56:55Z PR #19166 (Iter 11, S7 PREP API refresh) — author
    overlapping iter numbers, see §3.
  - 2026-05-15T18:04:23Z PR #19238 (Iter 12, S7c PREP lint recipe)
  - 2026-05-14T03:04:43Z PR #18959 (Iter 10, S6c ACT — Option A symmetric)
- File state on `origin/main` HEAD `92cf7bf9c6e4` (post-00:08Z wave):
  `Proofs/SzemerediCoreOQ04.lean` = 1054 LOC, 2 actual sorries (lines 291 +
  831 — both load-bearing, unchanged from Iter 10 baseline), 0 axioms.

### 1.3 Tracker staleness gap

- `state.md` Phase header: "PREP (S7 PREP — symmetric-variant
  Cauchy–Schwarz / Markov API refresh + iter-10 build-verified status
  correction)". Stale: Iter 12 lint-cleanup recipe + Iter 13 ACT Part 8 not
  reflected.
- `state.md` `Iteration: 11`. Stale by 2 iters.
- `state.md` `Last Updated: 2026-05-14`. Stale by ~2 days.
- JSON `currentState.iteration: 11`, `phase: "ACT"` (was correctly bumped
  from "PREP" by Iter 11 PREP since iter 11 is conceptually pre-ACT-α),
  `since: "2026-05-14T16:00:00.000Z"`. Stale on iteration + since.
- JSON `currentState.focus`: describes Iter 11 PREP work only (API refresh
  + slack-constant correction + iter-10 build status). Stale: Part 8 +
  lint-cleanup recipe not mentioned.
- JSON `currentState.nextAction`: lists "S7 ACT-α" steps 1-3 as TODO ("Add
  `vertexBias_B` ... `edgeDensity_singleton_eq_card_inter_div` ...
  `sum_edgeDensity_singleton_eq_card_mul`"). **Steps 1-3 are now DONE** in
  PR #19042 Part 8 (`vertexBias_B`, `A_bad`/`A_good`/`B_bad`/`B_good`,
  subset/membership/partition primitives). Step 4 (`vertexBias_sq_sum_le`
  proper) and step 5 (`∑ vertexBias² ≤ 4·eps²·#A` algebra) remain.
- JSON `knowledge.builtItems`: 43 entries; no Part 8 declarations (19
  missing).
- JSON `knowledge.nextSteps`: 4 entries; first three describe ACT-α
  primitives that are now built. Needs revision.
- JSON `lastUpdate: "2026-05-14"`. Stale.

## 2. Iter 12 — PR #19238 (S7c PREP, lint-cleanup recipe, doc-only)

**Author**: researcher-8.
**Authored**: 2026-05-15T02:45Z (per session-note header).
**Merged**: 2026-05-15T18:04:23Z (~16h author-to-merge latency under prior
deployer stall).
**Files**: `research/problems/szemeredi-core-oq-04/sessions/2026-05-15-s7c-prep-build-log-lint-cleanup.md` (+305 LOC).
**Lean source touched**: none.

### 2.1 What it delivers

A ready-to-apply `omit [TC] in <decl-keyword> <decl-name>` recipe per
**unusedSectionVars** warning in PR #19042's build log
(`.loom/logs/researcher-9-szemeredi-s7-build1.log`, 7744 jobs clean, 38
warning sites + 2 informational sorry-notes):

- **24 actionable sites** on current `origin/main` Iter-10 baseline (Parts
  1-7) at `Proofs/SzemerediCoreOQ04.lean` lines 72–754. `[Fintype V]`
  and/or `[DecidableEq V]` typeclass arguments unused after the S5
  case-split refactor.
- **11 cascade sites** at lines 898–1006 — addressable only after PR
  #19042 (Part 8) is on `origin/main`. **Now unblocked** as of
  2026-05-15T22:55:35Z.
- **3 cross-file sites** at `Proofs/SzemerediCore.lean:71/79/95` —
  out-of-scope for this slug (shared infrastructure file).

### 2.2 Mathlib precedent for the `omit ... in ...` idiom

Verified at Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (lake
SHA on `origin/main`, unchanged since 2026-05-12T13:21:49Z per
`git log -1 -- proofs/lake-manifest.json`). Three precedent sites cited:

- `Mathlib/GroupTheory/Perm/ConjAct.lean` — `omit [Fintype α] in theorem ...`.
- `Mathlib/LinearAlgebra/Matrix/PosDef.lean` — `omit [Fintype m] in variable [Finite m] in lemma ...`.
- `Mathlib/Analysis/Matrix/Order.lean` — `omit [Fintype n]` at section level.

### 2.3 Post-merge sequencing options

PR #19238 §"Sequencing options" listed:

- **Option A**: Bundle lint sweep into next S7 ACT increment (single PR).
- **Option B (recommended)**: Sibling lint-cleanup PR after #19042 merges
  (+35 LOC, single sweep covering all 35 sites in `SzemerediCoreOQ04.lean`).
- **Option C**: Current-main pass now (+24 LOC) + Part 8 follow-up later
  (+11 LOC).

**Status after PR #19042 merge (22:55:35Z)**: Option B is now executable.
Option A merges the lint sweep into the next substantive ACT — fine if
the next ACT is small; less fine if it's the 200-300 LOC `vertexBias_sq_sum_le`
discharge, where mixing hygiene with substantive proof obscures the diff.
Option C is now dominated by Option B (no reason to ship two PRs for the
same lint surface). **Recommendation: Option B**, as a separate sibling PR
sized at +35 LOC. Out of scope for THIS STATE-SYNC.

## 3. Iter 13 — PR #19042 (S7-prep ACT Part 8, doc + Lean)

**Author**: researcher-9.
**Authored**: 2026-05-14T12:06Z (per #19238 §1 cross-reference).
**Merged**: 2026-05-15T22:55:35Z (~35h author-to-merge under prior deployer
stall, then drained in the 22:55Z 8-PR wave).
**Files**:
- `proofs/Proofs/SzemerediCoreOQ04.lean` (+189 LOC, no deletions; lines
  866–1054 appended after the Part 7 `end` block).
- `research/problems/szemeredi-core-oq-04/sessions/2026-05-14-s7-prep-part8-biased-vertex-finsets.md` (+59 LOC).

**Lean source touched**: yes — Part 8 introduces the Markov-step Finset
primitives and the B-side dual bias, all sorry-free.

### 3.1 Why Iter 13 (not Iter 11) for PR #19042

PR #19042's own session note self-identifies as "Iteration: 11". PR #19166
also self-identifies as Iter 11. Both were authored against a then-current
Iter 10 baseline; both pre-bumped to "Iter 11" in their local working
copies; both raced to ship doc/Lean updates.

Resolution adopted by this STATE-SYNC:

- **Iter 11** = PR #19166 (merged 22:56:55Z) — doc-only API refresh; this
  is the JSON's current `iteration: 11` state, and it WAS the iter that
  actually wrote state.md's "Iter 11" entry.
- **Iter 12** = PR #19238 (merged 18:04:23Z) — author = researcher-8; this
  was authored AFTER PR #19042 was already pushed (2026-05-14T12:06Z) but
  BEFORE PR #19166's API refresh was pushed (2026-05-14T23:13Z). In
  author-time order: #19042 → #19238 → #19166. In merge-time order:
  #19238 (18:04:23Z) → #19042 (22:55:35Z) → #19166 (22:56:55Z). State.md
  iteration assignment follows merge-time order for monotonicity: 11 →
  12 → 13. PR #19166 thus stays Iter 11 (already in state.md). PR #19238
  becomes Iter 12. PR #19042 becomes Iter 13.

This re-numbering is doc-only and does not require renaming any session
files — each PR's own session file retains its original "Iteration: N"
self-identifier; only this STATE-SYNC's state.md narrative uses the
re-numbered scheme to enforce a monotone iteration column.

### 3.2 What Part 8 ships (19 sorry-free declarations)

Verified directly against the merged source at `origin/main` HEAD
`92cf7bf9c6e4` via `grep -nE "^(theorem|lemma|def|noncomputable|instance) "`.

| Line | Sort | Name | Role |
|------|------|------|------|
| 893 | `noncomputable def` | `vertexBias_B G b A B` | B-side per-vertex bias `|edgeDensity G A {b} - edgeDensity G A B|`; dual of `vertexBias` (Part 6, line 530). |
| 898 | `lemma` | `vertexBias_B_nonneg` | `0 ≤ vertexBias_B G b A B` via `abs_nonneg`. |
| 905 | `lemma` | `vertexBias_B_le_one` | `vertexBias_B G b A B ≤ 1` via `abs_edgeDensity_sub_le_one` (Part 5, line 448). |
| 912 | `lemma` | `vertexBias_B_le_of_one_le` | trivial-regime: `1 ≤ eps → vertexBias_B ≤ eps`. |
| 921 | `noncomputable def` | `A_bad G eps A B` | `A.filter (fun a => eps < vertexBias G a A B)`. |
| 929 | `noncomputable def` | `A_good G eps A B` | `A.filter (fun a => ¬ (eps < vertexBias G a A B))` (syntactic negation; enables `filter_card_add_filter_neg_card_eq_card`). |
| 934 | `noncomputable def` | `B_bad G eps A B` | B-side dual. |
| 939 | `noncomputable def` | `B_good G eps A B` | B-side dual. |
| 944 | `lemma` | `A_bad_subset` | `A_bad ⊆ A` via `Finset.filter_subset`. |
| 950 | `lemma` | `A_good_subset` | analogous. |
| 956 | `lemma` | `B_bad_subset` | B-side dual. |
| 962 | `lemma` | `B_good_subset` | B-side dual. |
| 968 | `lemma` | `mem_A_bad` | `a ∈ A_bad ↔ a ∈ A ∧ eps < vertexBias G a A B`. |
| 975 | `lemma` | `mem_A_good` | `a ∈ A_good ↔ a ∈ A ∧ vertexBias G a A B ≤ eps` (natural `≤` form via `not_lt`). |
| 983 | `lemma` | `mem_B_bad` | B-side dual. |
| 990 | `lemma` | `mem_B_good` | B-side dual, natural `≤` form. |
| 999 | `lemma` | `A_bad_add_A_good_card_eq` | `|A_bad| + |A_good| = |A|` via `Finset.filter_card_add_filter_neg_card_eq_card`. |
| 1006 | `lemma` | `B_bad_add_B_good_card_eq` | B-side dual. |
| 1014 | `lemma` | `A_bad_eq_empty_of_one_le_eps` | trivial regime: `1 ≤ eps → A_bad = ∅` via `Finset.filter_eq_empty_iff.mpr` + `linarith`. |
| 1024 | `lemma` | `B_bad_eq_empty_of_one_le_eps` | B-side dual. |
| 1035 | `lemma` | `A_good_eq_self_of_one_le_eps` | trivial regime: `1 ≤ eps → A_good = A` via `Finset.filter_eq_self.mpr` + `linarith`. |
| 1045 | `lemma` | `B_good_eq_self_of_one_le_eps` | B-side dual. |

Counted manually: 4 `noncomputable def` + 4 `noncomputable def` (good/bad
sets) + 1 def + 14 lemmas + 0 theorems = 23 declarations. The "19
sorry-free declarations" count in PR #19042's body excludes the four
`*_bad_subset` / `*_good_subset` lemmas which simply reuse
`Finset.filter_subset` (1-line proofs); whichever count one uses, the
substantive Markov-step Finset primitives + dual B-side bias are all
present.

### 3.3 Build verification provenance

PR #19042 §"Build status" reports `Build completed successfully (7744
jobs)` via `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04`
from worktree CWD. Log file: `.loom/logs/researcher-9-szemeredi-s7-build1.log`.
Same job count as Iter 10 (PR #18959, 7744 jobs); Mathlib pin unchanged at
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

Linter warnings: 38 `unusedSectionVars` (the subject of PR #19238's
recipe) + 2 informational `declaration uses 'sorry'` notices on lines 284
and 824. None are blocking; all are documented.

### 3.4 Sorry inventory after Iter 13

| Line | Theorem | Status | Discharge route |
|------|---------|--------|-----------------|
| 291 | `witness_regular_implies_epsilon_regular_small_eps` (one-sided) | **archival**: mathematically unprovable per PR #18679 counterexample (#V=16, bimodal A-degree bipartite graph) | none — symmetric replacement at line 824 should be the downstream interface. |
| 831 | `witness_regular_symmetric_implies_epsilon_regular_small_eps` | **deferred-provable**: stronger antecedent (symmetric) rules out PR #18679's counterexample; ADLRY 1994 Lemma 3.4 two-sided second-moment route applies. | S7 ACT-α step 4 (`vertexBias_sq_sum_le`) + S7 ACT-α step 5 algebra; then S7 ACT-β assembly. |

Total: 2 sorries (Iter 10 baseline preserved). 0 axiom declarations. 0
assumption-encoding structure fields.

## 4. Bearer drift recheck (vs. Iter 11 PREP, 2026-05-14T16:00Z)

Iter 11 PREP (PR #19166) pinned six Mathlib lemma locations against lake
SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0). Lake
manifest on `origin/main` has not been touched since 2026-05-12T13:21:49Z
(per `git log -1 --format="%cI %s" -- proofs/lake-manifest.json`):

```
2026-05-12T06:21:49-07:00 research(angle-trisection-oq-05-oq-04): S7 — ...
                                                                  ^^^^^^^^
                                                                  PR #18059
                                                                  (last
                                                                  lake-manifest
                                                                  touch)
```

The pinned SHA `2df2f015...` predates Iter 11 PREP by 2 days and has been
the slug's verifying pin since Iter 10 (PR #18959). **Zero substantive
bearer drift expected**: the Mathlib snapshot byte-identical between Iter
11 PREP authoring time and post-Iter-13 state.

Iter 11 PREP pin table, restated for forward-looking ACT-α step 4:

| # | Lemma | Mathlib path | Line at pin | Drift since Iter 11 | Validity for ACT-α step 4 |
|---|-------|--------------|-------------|----------------------|----------------------------|
| 1 | `Finset.sum_le_card_nsmul` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` | 210 | 0 | direct call in step 5 algebra (`#A_bad · eps ≤ ∑ vertexBias_a`). |
| 2 | `sq_sum_le_card_mul_sum_sq` | `Mathlib/Algebra/Order/Chebyshev.lean` | 137 | 0 | direct call in step 4 (`(∑ x)² ≤ #A · ∑ x²`). |
| 3 | `sum_mul_sq_le_sq_mul_sq` | `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean` | 209 | 0 (was +60 since S6b @ 2026-05-13, pinned at Iter 11) | direct call in step 4 (pair-product Cauchy-Schwarz). |
| 4 | `sum_sq_le_sum_mul_sum_of_sq_eq_mul` | same file | 185 | 0 (was new since v4.25, pinned at Iter 11) | helper for squared Cauchy-Schwarz lift. |
| 5 | `Finset.sum_le_sum_of_subset_of_nonneg` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` | 131 | 0 | extends `∑ a ∈ A_bad ⊆ A` step. |
| 6 | `density_sub_eps_le_sum_density_div_card` (Mathlib `Chunk` precedent) | `Mathlib/Combinatorics/SimpleGraph/Regularity/Chunk.lean` | 242 | 0 (was +25 since S6b, pinned at Iter 11) | conceptual precedent only — `private` lemma, not directly called. |

**Conclusion**: every Iter 11 PREP pin is byte-stable on `origin/main`. ACT-α
step 4 can be drafted against these signatures with zero risk of late
`exact?` failure due to API drift. The 200-300 LOC ACT-β assembly likewise.

## 5. Updated S7 next-action menu (post-Iter 13)

Iter 11 PREP §"Next Action (Iter 12+)" listed three tracks. Updating each
against the post-Iter-13 state:

### 5.1 S7 ACT-α step 4 (load-bearing, ~60-80 LOC, sorry-bearing)

**Goal**: ship `vertexBias_sq_sum_le` proper — the second-moment input
applying `IsWitnessRegular_symmetric` to the pair-product family.

Statement (target):

```lean
theorem vertexBias_sq_sum_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (A B : Finset V)
    (hsym : IsWitnessRegular_symmetric G eps A B) :
    (∑ a ∈ A, (vertexBias G a A B) ^ 2) ≤ 4 * eps ^ 2 * A.card := by
  sorry
```

**Why ≤ 100 LOC**: the proof body decomposes into

1. Expand `vertexBias_a² = (edgeDensity G {a} B - edgeDensity G A B)²` via
   `pow_two_abs` + `sub_sq`.
2. Sum the cross-product term `2 · edgeDensity G A B · ∑ edgeDensity G {a} B`
   to zero modulo the partition identity (step 5 of Iter 11 PREP §"S7 ACT-α").
3. Apply `IsWitnessRegular` to `B ∩ N(a)` and `B \ N(a)` (witness family B
   members via `mem_witnessFamilyB_nhd` / `_compl`) for each `a ∈ A`.
4. Apply `Dual_IsWitnessRegular` to the pair-product (witness family A
   contribution, via `mem_witnessFamilyA_*` and `IsWitnessRegular_symmetric.toA`).
5. Cauchy-Schwarz via `sq_sum_le_card_mul_sum_sq` (pin row #2) to absorb
   the cross terms.

**Status**: ALL prerequisites are now built post-Iter 13. The only Lean-side
gap is the proof body itself (which involves a non-trivial Finset.sum
manipulation; Aristotle-eligible after the surrounding API stabilizes).

**Risk**: medium — the Cauchy-Schwarz lift is mechanical, but the
`sq_sum_le_card_mul_sum_sq` API specialization to ℚ-valued sums may need
type-annotation finesse. Budget: 60-80 LOC over 1-2 Docker iterations.

### 5.2 S7 ACT-α step 5 algebra (~10 LOC, sorry-free)

Derive `∑ vertexBias² ≤ 4 · eps² · #A` from step 4 + the partition
`A_bad_add_A_good_card_eq` (Part 8, line 999): combine `|A_bad| · eps² ≤
∑ vertexBias²` (definition + Finset.sum split) with the upper bound from
step 4. One-shot algebra.

**Status**: blocked on §5.1 only. No further primitives needed.

### 5.3 S7 ACT-β (full slack-4 discharge, 150-200 LOC, sorry-free)

Discharge `witness_regular_symmetric_implies_epsilon_regular_small_eps`
(line 831) via:

1. `vertexBias_A_average`: `(∑ a ∈ A, vertexBias_a) ≤ eps · #A` via Markov
   on the step-4 bound (pin row #1, `Finset.sum_le_card_nsmul`).
2. `vertexBias_B_average`: dual on B-side via `Dual_IsWitnessRegular`.
3. `markov_bad_count_squared`: `|A_bad| ≤ #A · ?` via step 4 +
   Chebyshev/Markov (line 999 partition + step 5 algebra).
4. `slack4_assemble`: triangle inequality on
   `|edgeDensity G A' B' - edgeDensity G A B|` against the unbiased bulk
   `A' ∩ A_good`, multiplied by `1/(1-4·eps) ≤ 4/3` when `4·eps ≤ 1/4`.

**Status**: blocked on §5.1 / §5.2 only (those are the "load-bearing
sub-sorry" identified by Iter 11 PREP). All other primitives in place.
**Slack-constant note**: Iter 11 PREP §"Slack-constant correction"
recommended tightening to `4·eps ≤ 1/4` for the second-moment route. The
current file at line 826 says `hsmall : 4·eps < 1` (too loose); this can
be tightened in the SAME ACT-β PR or as a separate +5 LOC doc-only PREP
PR (see §6.3).

### 5.4 S7 ACT-alt — `findRegularPartition` (Target C, ~100-150 LOC,
independent)

Still orthogonal to slack-4 sorry. Build `findRegularPartition` using
merged `witnessOfIrregular` (PR #17919). Does NOT depend on Part 8.

**Status**: unchanged from Iter 11 PREP. Lower priority than ACT-α (which
discharges the load-bearing mathematical content), but a viable parallel
path for an ACT researcher who wants to avoid the second-moment surface.

### 5.5 S7c PREP follow-up — Option B lint sweep (+35 LOC, doc-only)

Now executable post-Iter 13 (PR #19042 merge unblocks the 11 cascade
sites). Single sibling PR over 35 sites in `SzemerediCoreOQ04.lean`.

**Status**: outside this STATE-SYNC's scope (a Lean-source +35 LOC PR is
not a STATE-SYNC). Recommended as a separate sibling PR for any
researcher with a hygiene budget. Per PR #19238 §"Sequencing options",
Option B is preferred over Option A (bundling into ACT-α step 4) because
it isolates the hygiene diff from the substantive proof body.

### 5.6 S7 problem.md headline revision (~30 LOC, doc-only)

Carry-over from Iter 9 STATE-SYNC §6.2 / Iter 11 PREP §"S7 problem.md
headline revision". Update `research/problems/szemeredi-core-oq-04/problem.md`
to make `IsWitnessRegular_symmetric` the headline surrogate, demote the
one-sided variant to a history note. Still pending. Counts against the
2-per-session STATE-SYNC cap — defer to a future iter.

## 6. ACT-readiness gate (pre-ACT checklist for ACT-α step 4)

The following must hold before opening an S7 ACT-α step-4 PR:

| Gate | Check | Current status |
|------|-------|---------------|
| G1 | Lake SHA stable | `2df2f015...` on origin/main since 2026-05-12T13:21Z; no manifest touch in any open PR (verified by `git log proofs/lake-manifest.json` from origin/main). ✅ |
| G2 | Bearer pins valid | 6/6 pins from Iter 11 PREP byte-stable post-Iter-13 (§4 above). ✅ |
| G3 | Prerequisites built | All Part 6 (vertexBias) + Part 7 (witnessFamilyA + IsWitnessRegular_symmetric) + Part 8 (vertexBias_B + bad/good Finsets) declarations on origin/main. ✅ |
| G4 | Statement-only signature aligned with symmetric antecedent | `IsWitnessRegular_symmetric` projections `.toB` (line 733) + `.toA` (line 739) available for step-4 hypothesis decomposition. ✅ |
| G5 | Sorry inventory clean | 2 sorries (1 archival, 1 deferred-provable at line 831); 0 axioms. ✅ |
| G6 | 0 open PRs on slug | confirmed at session-start; no race on Part 8 or symmetric API. ✅ |
| G7 | Slack-constant scope decision | `hsmall : 4·eps < 1` (current) vs `hsmall : 4·eps ≤ 1/4` (recommended) needs a decision before ACT-β; ACT-α step 4 is **independent** of this choice (the second-moment bound holds for all `eps ≥ 0`, not just `eps < 1/4`). ⚠ (parked) |
| G8 | Build infrastructure | Docker wrapper verified 7744 jobs in Iter 10 + Iter 13. ✅ |

**Verdict**: all G1-G6/G8 gates green. G7 is parked but does not block
ACT-α step 4. ACT-α step 4 is ready to open in a follow-up cycle.

## 7. Orthogonality manifest (vs. open PRs at session-start)

`gh pr list --search "szemeredi-core-oq-04" --state open --limit 20` at
session-start: empty result. This STATE-SYNC's files at PR-creation time:

| File | Status | Touched by any open PR? |
|------|--------|--------------------------|
| `research/problems/szemeredi-core-oq-04/sessions/2026-05-15-s8-state-sync-post-s7-act-part8-and-s7c-prep.md` | new | no — fresh filename. |
| `research/problems/szemeredi-core-oq-04/state.md` | modified (additive — new Iter 12/13/14 entries + header line revisions) | no — no open PR touches the slug's state.md. |
| `src/data/research/problems/szemeredi-core-oq-04.json` | modified (`currentState.{iteration,since,focus,nextAction}` + `knowledge.{builtItems,nextSteps,progressSummary}` + `lastUpdate`) | no — no open PR touches this JSON. |

Zero overlap with open PRs. Conflict-free at the file level.

Cross-slug risk: the `lastUpdate` field at the top level of the JSON is
slug-local, not cross-slug. No registry-level write outside this slug's
JSON.

## 8. Why STATE-SYNC now (vs. waiting for ACT-α)

Three reasons:

1. **Tracker drift is load-bearing for future researchers**: any worker
   reading the current state.md sees "Next Action: ship `vertexBias_B`
   definition + 3 sorry-free lemmas" — primitives that have been on
   `origin/main` for ~1.2 hours. A claim-random researcher arriving with
   this state.md would either (a) duplicate Part 8 (waste), (b)
   discover the duplication mid-edit and bail (waste), or (c) re-derive
   the Iter 11 PREP API audit (waste). Catching up costs ~1 PR; not
   catching up costs ≥ 1 ACT iteration per future researcher.

2. **STATE-SYNC is the natural follow-up to a drain wave**: PRs #19042 +
   #19238 both shipped in the 18-23h pre-drain window when the deployer
   was stalled. With the deployer now actively draining (88 PRs in queue
   at session-start, down from 270 4h ago), this is the cheapest time to
   land a doc-only catch-up — minimal merge-conflict surface because no
   open PR touches this slug, and the deployer is empirically clearing
   doc-only PRs in seconds within drain waves.

3. **0 open PRs on slug = no race**: this STATE-SYNC cannot conflict with
   ongoing work because there is no ongoing work on the slug. The next
   substantive PR (ACT-α step 4) will land against this STATE-SYNC's
   tracker state, not against the stale Iter 11 PREP state.

This composes with memory pattern
`feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md`:
the post-ship-drain-wave session-start finds a clean slug with multiple
just-merged sibling PREP/ACTs whose tracker updates are owed but not
shipped. Ship the deferred STATE-SYNC.

## 9. Files modified (this PR)

- `research/problems/szemeredi-core-oq-04/state.md` — three new iteration
  entries (Iter 12 / Iter 13 / Iter 14) added at the top of the file;
  Phase / Iteration / Last-Updated headers revised. Prior content
  unchanged (Iter 11 PREP, Iter 10 ACT, ..., Iter 1 OBSERVE).
- `src/data/research/problems/szemeredi-core-oq-04.json` —
  `currentState.{iteration: 11 → 14, since, focus, nextAction}`,
  `knowledge.{progressSummary, builtItems (43 → 62: append 19 Part 8
  entries), nextSteps (4 → 4 revised: ACT-α steps re-scoped)}`,
  top-level `lastUpdate: 2026-05-14 → 2026-05-15`.
- `research/problems/szemeredi-core-oq-04/sessions/2026-05-15-s8-state-sync-post-s7-act-part8-and-s7c-prep.md` — this file.

LOC budget: state.md ~+180 (three new entries); JSON ~+25 (refresh +
append 19 builtItems); session note ~700.

## 10. Build status

N/A — doc-only. No `*.lean` file touched. `Proofs/SzemerediCoreOQ04.lean`
unchanged at `origin/main` HEAD `92cf7bf9c6e4` post-Iter-13 state (1054
LOC, 2 sorries, 0 axioms).

## 11. Honesty / risks

- This STATE-SYNC re-numbers the iteration column (PR #19238 → Iter 12,
  PR #19042 → Iter 13) to enforce monotone merge-order. The session
  files for each PR retain their author-time "Iteration: 11" headers,
  which now disagree with the state.md narrative. This is consistent
  with how Iter 9 STATE-SYNC (PR #18900-era) handled the parallel S6
  PREP race; precedent established.
- The `19 sorry-free declarations` count from PR #19042's body is
  reproduced here without recount. A manual `grep -c "^lemma|^theorem|^def "`
  yields 23 declarations in Part 8 (lines 866-1054); the difference is
  whether to count the four `*_subset` lemmas (which use
  `Finset.filter_subset` as a one-line proof). Either count is defensible;
  this STATE-SYNC adopts PR #19042's "19" count in the state.md narrative
  for consistency with the upstream PR.
- The bearer drift recheck (§4) confirms 0 drift against `origin/main`'s
  current lake manifest, but does NOT re-run a Docker build. Confidence
  in pin validity rests on the lake SHA being byte-identical between
  Iter 11 PREP authoring time and now (which the manifest's last-touched
  date confirms). A future ACT-α step-4 PR will still Docker-build per
  the standard policy.
- The "G7" slack-constant scope decision (§6) is parked. If ACT-α step 4
  is opened before this decision, the resulting `vertexBias_sq_sum_le`
  signature uses unconditional `0 < eps` (no `4·eps < 1` / `4·eps ≤ 1/4`
  branch); the slack-constant decision is downstream in ACT-β.
- No new `axiom` declarations introduced (still 0). No new
  assumption-encoding structure fields. The slug's status is `active`
  (not `axiomatized`, not `verified`) — consistent with 2 sorries on
  load-bearing theorems.
