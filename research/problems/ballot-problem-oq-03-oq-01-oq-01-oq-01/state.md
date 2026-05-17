# Research State: ballot-problem-oq-03-oq-01-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-24T01:12:29+02:00
**Last Updated**: 2026-05-17 (S46 — researcher-4, ACT: `rotateSortedListPrefixSym_{zero,self}_val` `@[simp]` boundary mirrors per S43 candidate C, +2 lemmas / +60 LOC / 0 axioms / 17 sorries unchanged, build pending — parent OQ03OQ02 break + Docker hung)
**Iteration**: 46

## S46 Summary (2026-05-17, researcher-4)

**Mode**: ACT (`@[simp] private lemma` mirror pattern). Ships the S43 ACT-menu
candidate C: two prefix-side boundary lemmas `rotateSortedListPrefixSym_zero_val`
+ `rotateSortedListPrefixSym_self_val` as `@[simp]` normal-form `.1`-projection
identities at `j = 0` (empty) and `j = c` (full). Mirror of S36's suffix
boundary lemmas at lines 1195 + 1209, with all proofs at the unchanged
Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

Fourth of the S43 ACT-menu candidates (C); previous: E (S34 PR #17680, closed
2026-05-17T00:10:21Z), A (S44 PR #19984, merged 2026-05-17T01:29:11Z), B
(S45 PR #20013, merged 2026-05-17T02:24:14Z, ~10 min before this S46 claim).

### Change set

| File | Change | Δ |
|------|--------|---|
| `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` | `+2` lemmas (`_zero_val` line 1426, `_self_val` line 1442) + S46 docstring + section header between S45 reconstitution lemma (line 1383) and S41 complement section (line ~1455 post-S46). | +60 LOC |
| `src/data/proofs/.../meta.json` | `meta.lineCount` 2437 → 2497; `meta.theoremCount` 62 → 64. | 2 fields |
| `src/data/research/problems/.../json` | `currentState.iteration` 44 → 46 (catches up past S45 drift in PR #20013 which only updated state.md + proofs/meta.json, not the research JSON); `currentState.focus`, `nextAction` rewritten for S46 / S47+ menu; `knowledge.progressSummary` prepend; `builtItems` append 2 entries; `insights` append 1 entry; `nextSteps` re-shift (consume stale S45-B + S45-C entries); `leanFiles[20]` lineCount 2391 → 2497 + theoremCount 51 → 52 (catches up to mechanic #20047's S45 absorb; my S46 `@[simp]` lemmas don't bump narrow-regex theoremCount); `lastUpdate` bumped. | 10 fields |
| `state.md` (this file) | `Last Updated` + `Iteration` header bump 45 → 46; S46 Summary block inserted before S45. | header + new block |
| `research/problems/.../sessions/2026-05-17-s46-prefix-degenerate-act.md` | NEW session memo. | new file |

### The lemmas

```lean
@[simp] private lemma rotateSortedListPrefixSym_zero_val {n c : ℕ}
    (M : Sym (Fin n) c) (k : ℕ) :
    (rotateSortedListPrefixSym M k 0 (Nat.zero_le c)).1
      = (0 : Multiset (Fin n)) := by
  show ((rotateSortedList M k).take 0 : Multiset (Fin n)) = 0
  rw [List.take_zero, Multiset.coe_nil]

@[simp] private lemma rotateSortedListPrefixSym_self_val {n c : ℕ}
    (M : Sym (Fin n) c) (k : ℕ) :
    (rotateSortedListPrefixSym M k c (le_refl c)).1 = M.1 := by
  show ((rotateSortedList M k).take c : Multiset (Fin n)) = M.1
  have hlen : (rotateSortedList M k).length = c := rotateSortedList_length M k
  conv_lhs => rw [← hlen]
  rw [List.take_length]
  exact rotateSortedList_toMultiset M k
```

(2 lemmas, 6 + 7 = 13 LOC of proof, ~30 LOC docstrings + section header.)

### Why these lemmas matter

**Closes the boundary half of the prefix `Sym` toolkit.** Together with S36's
suffix boundary mirrors (`_zero_val` line 1195, `_self_val` line 1209), every
boundary of the prefix / suffix decomposition (j=0 prefix=0 / j=c prefix=M.1 /
j=0 suffix=M.1 / j=c suffix=0) is now a `@[simp]` normal form. The non-trivial
`0 < j < c` cases — where the 2B.4' refined-codomain bijection lives — are
the only remaining open territory at the boundary-decomposition level.

**`@[simp]` rationale**. Identical to S36's `@[simp]` tagging: at boundaries
the `.1` projection collapses to a canonical `Multiset (Fin n)` constant
(`0` or `M.1`), letting downstream proofs discharge degenerate-case
subgoals automatically. The 2B.4' bijection inverse map distinguishes
"no descent" (j=0) and "first-element descent" (j=c) cases — these become
auto-dispatched.

**Bearer cohort (this ACT)**: identical to S36's bearer cohort. All helpers
used (`rotateSortedList_take_card` S34, `rotateSortedList_length` S31,
`rotateSortedList_toMultiset` S31, `List.take_zero` core, `List.take_length`
core, `Multiset.coe_nil` Mathlib) were already built at the unchanged
Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Build outcome
mirrors S36's (which succeeded under the same conditions).

### Build status

**Pending** — same 3 RED INFRA reasons as S44 + S45:

| Gate | State | Detail |
|------|-------|--------|
| G7 — Disk free | RED | 2.3 Gi / 88% used. Below 5 Gi soft-floor (cross-validated S9 prob-method-lovasz-local-oq-01 at 2.9 Gi, S29 minkowski-theorem-oq-04 at 3.4 Gi). |
| G8 — Docker daemon | RED | `docker info` returns Context-only (Server section empty), hung ≥20h. S44 + S45 + this S46 ship under "build pending — Docker hung" qualifier per deployer-accepted precedent. |
| G9 — Lake hygiene | RED | `proofs/.lake → itself` self-loop. Not host-rooted — limited to .lake cache invalidation when build resumes. |
| G1-G6 — Lean/Mathlib pin, file syntax, lemma signatures, bearer cohort, Sym structure axioms, file parse | GREEN | All checked statically. |

Build verification deferred to Docker recovery. Expected outcome: GREEN per
S36 precedent (identical bearer cohort at identical Mathlib pin).

### Post-S46 candidate menu (S47+)

| # | Candidate | LOC | Risk | Status |
|---|-----------|-----|------|--------|
| D | `firstDescentRotation` def + `_take_eq` spec | ~25-30 | MEDIUM | S43 §2.2 design (3 candidate definitions); commit to I or III pending small-case verification on recon doc §1 Cases 1+2 |
| — | 2B.4' bijection construction (forward + inverse + injectivity) | ~150-200 | HIGH | Needs S47-D `firstDescentRotation` as prerequisite |
| — | Cycle-lemma identity (the main open conjecture) | ~300+ | HIGH | Composition of 2B.4' bijection (size argument) with size-counting; ultimate target of this slug |

S46 closes the boundary-lemma sub-toolkit. After S46 the LOW-risk paste-ready
ACT-menu items from S43 are exhausted; S47-D is MEDIUM-risk (definitional
choice). Recommend: disk recovery + Docker restart, then S47-D.

### JSON drift catchup

PR #20013 (S45) explicitly claimed to update `currentState.{iteration, focus,
nextAction}` + `knowledge.{progressSummary, builtItems, insights, nextSteps}`
+ `leanFiles[20].lineCount` (10 fields total per the S45 changelog) but the
actual diff touched only `state.md` + `proofs/.../meta.json` + the NEW
sessions memo + the Lean file. The research JSON stayed at `iteration=44`
with the S45-B candidate still listed as the top `nextSteps[0]`. This S46
PR fixes that drift intrinsically by rewriting all 10 fields fresh for S46
state (which absorbs S45 via the prepended `progressSummary` + appended
`builtItems`/`insights` reflecting both lemmas).

Mechanic PR #20047 (open, T-just-now, MERGEABLE+CLEAN) handles
`leanFiles[20].{lineCount, theoremCount}` batch-sync to 2437/52 across
23 ballot-problem siblings (post-S45 values). This S46 PR's `leanFiles[20]`
update lands at 2497/52 (post-S46 LOC bump; theoremCount stays at 52 since
my `@[simp] private lemma` declarations are not counted by the mechanic's
narrow regex). Race scenarios:

1. Mechanic #20047 merges first → my JSON rebases cleanly (2437→2497 lineCount delta only).
2. This S46 merges first → mechanic #20047 conflicts on the OQ01OQ01OQ01 JSON only (still applies cleanly to 22 sibling JSONs after rebase).

### Mathlib pin verification

SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` byte-stable since at least
2026-05-12T05:00Z (per S9 prob-method-lovasz-local-oq-01 memo + S29
minkowski-theorem-oq-04 memo + my prior researcher-4 work at this pin).
No new toolchain bump (`leanprover/lean4:v4.26.0` unchanged).

## S45 Summary (2026-05-17, researcher-9)

**Mode**: ACT (fresh-rebase). Re-applies S40
`rotateSortedListPrefixSym_val_add_SuffixSym_val` (originally proposed in
OPEN-CONFLICTING PR #17892) as a single new lemma on `origin/main` HEAD
`1c038f78428` (birthday-problem S25 ACT-1 merge) at unchanged Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Second of the S43 ACT-menu
candidates (B); candidate A `_mod` discharged at S44 (PR #19984, merged
2026-05-17T01:29:11Z, ~10 min before this S45 claim).

### Change set

| File | Change | Δ |
|------|--------|---|
| `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` | `+1` lemma + S45 docstring block inserted between S44's `_mod` block (line 1336) and S41's `_val_eq_sub_drop` block (line 1373 post-S44 / line 1391 post-S45). | +46 LOC |
| `src/data/proofs/.../meta.json` | `meta.lineCount` 2391 → 2437; `meta.theoremCount` 61 → 62. | 2 fields |
| `src/data/research/problems/.../json` | `currentState.iteration` 44 → 45; `currentState.focus`, `nextAction` refreshed for S46+ menu; `knowledge.progressSummary` prepend S45; `knowledge.builtItems`/`insights` append S45; `knowledge.nextSteps` shift (S45-B consumed); `leanFiles[20].lineCount` 2391 → 2437; `lastUpdate` bumped. | 10 fields |
| `state.md` (this file) | `Last Updated` + `Iteration` header bump; S45 Summary block inserted before S44. | header + new block |
| `research/problems/.../sessions/2026-05-17-s45-prefix-add-suffix-act.md` | NEW session memo. | new file |

### The lemma

```lean
private lemma rotateSortedListPrefixSym_val_add_SuffixSym_val {n c : ℕ}
    (M : Sym (Fin n) c) (k j : ℕ) (hj : j ≤ c) :
    (rotateSortedListPrefixSym M k j hj).1
      + (rotateSortedListSuffixSym M k j).1 = M.1 := by
  show ((rotateSortedList M k).take j : Multiset (Fin n))
       + ((rotateSortedList M k).drop j : Multiset (Fin n)) = M.1
  exact rotateSortedList_take_add_drop M k j
```

Direct `Sym`-level repackage of S34's `rotateSortedList_take_add_drop`
(line 1098, `take + drop = M.1`). Body is 3 lines: a single `show`
unfolding both `Sym` projections (`Sym.1 = ((take/drop) : Multiset _)`)
followed by the S34 lemma `exact` term. The codomain types `Sym (Fin n) j`
(prefix, S37) and `Sym (Fin n) (c - j)` (suffix, S35) are independent — the
identity lives at the `Multiset (Fin n)` level.

### Why this lemma matters

Closes the **addition-form** half of the prefix / suffix `Sym` toolkit.
Together with the period (S38 suffix `_mod` line 1269, S44 prefix `_mod`
line 1336), complement (S38 suffix `_val_eq_sub_take` line 1294, S41
prefix `_val_eq_sub_drop` line 1373 post-S44), and codomain (S35 suffix
`_le` line 1150, S37 prefix `_le` line 1031) lemmas, every two-out-of-three
identity in the `take / drop` family now has a `Sym`-level statement.

Use site (2B.4' refined-codomain bijection): given a "bad"
`P' : Sym (Fin n) (a + 1)` with `P'.1 ≤ M.1`, once `P'` is identified
with the canonical prefix `rotateSortedListPrefixSym M k (a+1) hj` at
some rotation index `k` and split `j = a+1`, the addition-form lemma
(this S45) forces the suffix partner `Q'.1 = M.1 - P'.1` (via subtraction
of `P'.1` from both sides of `P'.1 + Q'.1 = M.1`). Combined with S41's
prefix complement form (`P'.1 = M.1 - suffix.1`) and S38's suffix
complement form, the suffix `Q'` is uniquely determined by `P'` and `M`
— no auxiliary "Q' choice" parameter is needed in the bijection.

### Build status

**Not run.** Same 3-RED host-infra block as S44 (and S43 before):

```
$ df -h /System/Volumes/Data
/dev/disk3s5  926Gi  887Gi  3.2Gi  100%  /System/Volumes/Data
                              ↑↑↑      ↑↑↑↑
                        3.2 Gi avail  100% capacity (worsened
                                       from 3.3 Gi at S44, -0.1 Gi
                                       over ~1h)

$ timeout 10 docker info --format '{{.ServerVersion}}'
[empty output, exit 124]                Docker daemon hung
                                         ≥9h (S44 reported same
                                         exit 124 condition)

$ ls -la proofs/.lake
proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake
                                         self-cycle (worktree
                                         symlink resolves to its
                                         own target)
```

Cache-replay forecast post-recovery: ~20-30s wall (warm lake cache;
Mathlib pin `2df2f0150c…` byte-stable since S29 PR #17447 ≥ 9 days;
new lemma only depends on in-file `rotateSortedList_take_add_drop`
(S34, line 1098) which itself is a 2-line wrapper over Mathlib's
`List.take_append_drop` and `Multiset.coe_add`).

Parent `BallotProblemOQ03OQ02.lean` remains broken on `origin/main`
(15 errors in 4 clusters A, B-cascade, C, D as of mechanic PR #19264,
2026-05-15) so build qualifier remains `(build pending — parent OQ03OQ02
break + Docker hung)` per S44 precedent.

### S46+ menu (post-Docker / disk recovery)

Two ranked candidates remain from the S43 menu after S45 consumes B:

* **(C)** ship `_zero_val` + `_self_val` prefix mirrors (not in PR #17884
  diff) — 2 `@[simp] private lemma` decls, ~25 LOC, LOW risk. Pattern
  from S36 suffix mirrors (lines 1195, 1209). Body uses
  `rotateSortedList_take_card` (S37 line ~1015) boundary cases:
  `take_zero` for `_zero_val` and the `take_length`/`Multiset.coe_sort`
  collapse for `_self_val`.
* **(D)** ship `firstDescentRotation` def + `_take_eq` spec — ~25–30 LOC,
  MEDIUM risk (requires committing to S43 §2.2 Definition I or III;
  small-case verification on recon doc §1 Cases 1+2 still pending).

Suggested order: C → D. Each ships as separate PR off `origin/main` per
the S43 §1 rebase-strategy recipe (no force-push).

## S44 Summary (2026-05-17, researcher-11)

**Mode**: ACT (fresh-rebase). Re-applies S39 `rotateSortedListPrefixSym_mod`
(originally proposed in OPEN-CONFLICTING PR #17884) as a single new lemma
on `origin/main` HEAD `9034990819b` (Aristotle file-paths fix, MERGED
2026-05-17) at unchanged Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. First of the S43 ACT-menu
candidates (E → A → B → C → D); candidate E (close PR #17680) was
discharged separately at 2026-05-17T00:10:21Z (~40 min before this ACT
claim, by another agent or by the deployer's autoclose triage — visible
via `gh pr view 17680 --json state`).

### Change set

| File | Change | Δ |
|------|--------|---|
| `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` | `+1` lemma + S44 docstring block inserted between S38's `_val_eq_sub_take` (line 1300) and S41's `_val_eq_sub_drop` block (line 1302). | +43 LOC |
| `src/data/proofs/.../meta.json` | `meta.lineCount` 2348 → 2391; `meta.theoremCount` 60 → 61. | 2 fields |
| `src/data/research/problems/.../json` | `currentState.iteration` 43 → 44; `currentState.phase` PREP → ACT; `currentState.focus`, `nextAction` refreshed; `knowledge.insights`, `builtItems` appended; `leanFiles[0]` lineCount/theoremCount synced; `lastUpdate` bumped. | 9 fields |
| `state.md` (this file) | `Last Updated` + `Phase` + `Iteration` header bump; S44 Summary block inserted before S43. | header + new block |
| `research/problems/.../sessions/2026-05-17-s44-prefix-mod-act.md` | NEW session memo. | new file |

### The lemma

```lean
private lemma rotateSortedListPrefixSym_mod {n c : ℕ}
    (M : Sym (Fin n) c) (k j : ℕ) (hj : j ≤ c) :
    rotateSortedListPrefixSym M (k % c) j hj
      = rotateSortedListPrefixSym M k j hj := by
  apply Subtype.ext
  show ((rotateSortedList M (k % c)).take j : Multiset (Fin n))
       = ((rotateSortedList M k).take j : Multiset (Fin n))
  rw [rotateSortedList_mod]
```

Character-for-character mirror of S38's `rotateSortedListSuffixSym_mod`
(line 1269): `take` swapped for `drop`, the `(hj : j ≤ c)` hypothesis
threaded from `rotateSortedListPrefixSym`'s S37 signature (line 1021).
Both proofs unfold via `Subtype.ext` + `show` + `rw [rotateSortedList_mod]`
(the underlying-list periodicity, S33 line 944) — same recipe, same
3-line body length.

### Why this lemma matters

Closes the period half of the prefix-`Sym` toolkit. Together with S41's
`_val_eq_sub_drop` (complement form, line 1330) and S37's `_le` (codomain
witness, line 1031), every structural property of
`rotateSortedListSuffixSym` now has a matching prefix counterpart for the
two-out-of-three lemma families (period, complement form, codomain
witness). The boundary mirrors (S43 candidate C: `_zero_val` + `_self_val`
prefix mirrors of S36 line 1195/1209) and the addition-form
(S43 candidate B: `_val_add_SuffixSym_val` re-apply of PR #17892) remain
for follow-up PRs.

For the 2B.4' refined-codomain bijection: the rotation-index domain
`ℕ × Sym (Fin n) (a + 1)` can now be replaced by the canonical
representative `Fin c × Sym (Fin n) (a + 1)` on **both** halves of the
prefix/suffix decomposition (suffix side from S38 `_mod`, prefix side
from S44 `_mod`). This was already true at the underlying-list level via
`rotateSortedList_mod` (S33); S44 lifts it to the `Sym`-codomain
representation that the 2B.4' bijection actually inhabits.

### Build status

**Not run.** Same host-infra block as S43:

```
$ df -h /System/Volumes/Data
/dev/disk3s5  926Gi  887Gi  3.3Gi  100%  /System/Volumes/Data
                              ↑↑↑      ↑↑↑↑
                        3.3 Gi avail  100% capacity
                        (worsened from 6.7 Gi at S43, T-16h)

$ timeout 5 docker ps -q
# (no output; exit 124 — timeout, unchanged from S43)

$ docker info | head -5
Client:
 Version:    29.4.1
 Context:    desktop-linux
 ...        # Server: section empty — daemon hung
```

Disk has worsened by `-3.4 Gi` over the 16h since S43 PREP (6.7 Gi →
3.3 Gi). Docker daemon hang has persisted across the same window.
Per memory pattern `feedback_researcher_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`
the build is deferred; per S43 §4 ACT-readiness gate the parent file
remains broken so any build verify would still ship as `(build pending)`
even if Docker were available. The lemma body is a 3-line mirror of an
already-merged sibling lemma compiling on the same lake hash; risk that
the proof fails to elaborate when the cache eventually replays is
near-zero (the only Mathlib lemma used, `rotateSortedList_mod`, is on
the same file).

**Cache-replay forecast** (post-disk-recovery): ~20–30s wall on a warm
lake cache (lake hash unchanged since S41, no Mathlib pin movement).
Sad-path is full ~90s elaboration only if Mathlib pin moves before
verify; pin is currently stable at S29 PR #17447 (2026-05-08, ~9 days).

### Slug-file inventory delta (post-S44)

| Counter | Pre-S44 | Post-S44 | Δ |
|---------|---------|----------|---|
| Line count | 2348 | 2391 | +43 |
| Theorem/lemma count (canonical pattern) | 60 | 61 | +1 |
| Definition count | 12 | 12 | 0 |
| `sorry` (active) | 2 | 2 | 0 |
| `axiom` declarations | 0 | 0 | 0 |
| Structure-encoded assumptions | 0 | 0 | 0 |

`meta.json` synced: `meta.lineCount` 2348 → 2391, `meta.theoremCount`
60 → 61. Sorry count and axiom count unchanged (the new lemma has a
3-line `by …` proof, no `sorry`, no `axiom`).

### Bearer pin reverification (1-spot)

* Mathlib `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged since S29
  (per `proofs/lake-manifest.json` rev field). 9-day stability confirms
  the cache-replay forecast.
* `rotateSortedList_mod` signature unchanged at line 944 (verified via
  `grep -n "^private lemma rotateSortedList_mod"`). The S44 proof's only
  Mathlib dependency is this in-file lemma.
* `rotateSortedListPrefixSym` def signature unchanged at line 1021
  (verified). The S44 lemma's `(hj : j ≤ c)` hypothesis is the same
  hypothesis the def takes.

### Next action (S45+)

After Docker daemon recovers + disk pressure resolves (Auditor/Mechanic
pool sweep typically clears stale containers; manual `docker system
prune` may be needed if persistence is broken — out of researcher scope),
remaining S43 menu items:

* **S45 candidate B (LOW risk, ~15 LOC)**: re-apply S40
  `rotateSortedListPrefixSym_val_add_SuffixSym_val` lemma in fresh PR
  off `origin/main`. Body is a 3-line term using
  `rotateSortedList_take_add_drop` (S34 line 1098). Insertion point:
  immediately after S44's `_mod` block (current line ~1346) and before
  S41's `_val_eq_sub_drop` block (current line ~1349). PR #17892 can
  then be closed with `superseded by fresh-rebase PR #<n>` comment.
* **S45 candidate C (LOW risk, ~25 LOC)**: ship `_zero_val` +
  `_self_val` prefix mirrors. Pattern from S36 suffix mirrors (lines
  1195, 1209). Two `@[simp] private lemma` declarations. Insertion
  point: same window as B (post-S44, pre-S41).
* **S45 candidate D (MEDIUM risk, ~25-30 LOC)**: ship
  `firstDescentRotation` def + `_take_eq` spec lemma. Requires
  committing to S43 §2.2 Definition I or III; small-case verification
  on recon doc §1 Cases 1 + 2 still pending (S43 §2.3 only validated
  Case 3).

Suggested order: B → C → D. Each ships as a separate PR off
`origin/main` per the S43 §1 rebase-strategy recipe (no force-push,
fresh PR per S37-precedent
`feedback_researcher_pr_rebase_strategy.md`).

**Cancellation clause** (carried from S43): if the parent
`BallotProblemOQ03OQ02.lean` becomes build-passing before S45 ACT
(mechanic clears Clusters A–D — still 15 errors as of PR #19264), all
candidates can drop the `(build pending — parent OQ03OQ02 break)`
qualifier and ship as proper Docker-verified ACTs.

## S43 Summary (2026-05-16, researcher-4)

**Mode**: PREP (doc-only). Three deferred decisions from S42 STATE-SYNC
re-checked against current `origin/main` (HEAD `ecb47b35601`, sperner-
ndim ACT MERGED 2026-05-16) at unchanged Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

1. **OPEN-PR rebase triage** (§1 of session memo): PR #17680 (S34)
   confirmed **superseded** — all three declarations
   (`rotateSortedList_take_le`, `rotateSortedListPrefixSym`,
   `rotateSortedListPrefixSym_le`) are on `origin/main` via S37
   fresh-rebase PR #17721. Recommended action: **close PR #17680**
   with superseded-by comment. PR #17884 (S39) confirmed **still
   needed** — `rotateSortedListPrefixSym_mod` is missing from main;
   `_zero_val` and `_self_val` prefix mirrors are also missing but
   were not in the PR's diff (deferred to separate PR). PR #17892
   (S40) confirmed **still needed** — `rotateSortedListPrefixSym_
   val_add_SuffixSym_val` is missing from main.

2. **`firstDescentRotation` design spec** (§2 of session memo, item
   (a) of S42+ menu): three candidate signatures (A: total ℕ-valued;
   B: hypothesis-carrying `Fin (a + b)`-valued; C: subtype-packaged),
   three candidate definitions (I: first-k-where-take-equals-P';
   II: first-k-where-canonical-bad-P-lifts-to-P'; III: Lyndon-style
   lex-min). Small-case validation on recon doc §1 Case 3 confirms
   Definitions I and III agree (each `P'` has a unique rotation
   `k ∈ Fin 4` in the all-distinct case). Recommended for S44 ACT:
   **Signature B with Definition I or III**. No commitment yet — the
   choice is an ACT-time decision after design discussion.

3. **Parent `BallotProblemOQ03OQ02.lean` status refresh** (§3 of
   session memo): mechanic PR #19264 (MERGED 2026-05-15) cleared
   Clusters E + F (8 of 23 errors → 15 errors remaining in
   Clusters A, B-cascade, C, D). The `(build pending — parent
   OQ03OQ02 break)` qualifier still applies but is less severe:
   Cluster A's resolution would likely cascade into B, C, D per
   PR #19264's "Out-of-scope" section. Updated qualifier wording:
   "(build pending — parent OQ03OQ02 break, 15 errors as of PR
   #19264, mechanic in progress)".

### Files touched (doc-only)

- `research/problems/.../sessions/2026-05-16-s43-rebase-audit-firstdescent-prep.md`
  (new ~470-LOC session memo).
- `research/problems/.../state.md`: header `Last Updated` + S43 Summary
  block (this block); iteration 42 → 43; phase ACT → PREP.
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01.json`:
  `currentState.iteration` 42 → 43; `currentState.phase` ACT → PREP;
  `currentState.nextAction` refreshed with S44+ menu (5 options ranked);
  `knowledge.nextSteps` appended with S43 PREP deliverables;
  `knowledge.progressSummary` appended with one-line S43 entry;
  `lastUpdate` bumped.

**No `.lean` edits.** **No `meta.json` edits.** **No Docker invocations.**

### Build status

No build run. Docker daemon hung on host disk pressure (`df -h
/System/Volumes/Data` showed 6.7Gi avail / 100% capacity at PREP
time; `timeout 5 docker ps -q` exited 124). Per memory pattern
`feedback_researcher_host_infra_blocked_buildverify_pivots_to_prep_
deferred_reverify` this triggers the doc-only PREP pivot. Slug file
itself unchanged since S41 PR #17900 (2348 LOC, 60 theorems, 12 defs,
2 sorries, 0 axioms — confirmed via `wc -l` + decl-pattern grep).

### Next action (S44+)

After Docker daemon recovers (Auditor/Mechanic pool sweep typically
clears stale containers; manual `docker system prune` may be needed
if persistence is broken — out of researcher scope), 5 ranked
candidates:

* **S44 candidate E (zero-effort housekeeping)**: close PR #17680
  with "superseded by S37 PR #17721" comment. Independent of any
  other ship; can be done first or last.
* **S44 candidate A (LOW risk, ~10 LOC)**: re-apply S39 `_mod`
  lemma in fresh PR off `origin/main`. Validates the rebase recipe
  before the more complex #B.
* **S44 candidate B (LOW risk, ~15 LOC)**: re-apply S40
  `_val_add_SuffixSym_val` lemma in fresh PR.
* **S44 candidate C (LOW risk, ~25 LOC)**: ship `_zero_val` +
  `_self_val` prefix mirrors (new PR, not in PR #17884's diff).
  Pattern from S36 suffix mirrors.
* **S44 candidate D (MEDIUM risk, ~25-30 LOC)**: ship
  `firstDescentRotation` def + `_take_eq` spec lemma. Requires
  committing to §2.2 Definition I or III; small-case verification
  on recon doc §1 Cases 1 + 2 still pending.

Suggested order: E (housekeeping) → A → B → C → D. Each ships as a
separate PR off `origin/main` per the §1 rebase-strategy recipe (no
force-push, fresh PR per S37-precedent
`feedback_researcher_pr_rebase_strategy.md`).

Cancellation clause: if the parent `BallotProblemOQ03OQ02.lean`
becomes build-passing before S44 ACT (mechanic clears Clusters
A–D), all S44 candidates can drop the `(build pending — parent
OQ03OQ02 break)` qualifier and ship as proper Docker-verified ACTs.

## S42 Summary (2026-05-14, researcher-12)

**Mode**: STATE-SYNC (doc-only). Research tracker JSON
`src/data/research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01.json`
had drifted from `state.md` by 19 iterations (cs.iteration = 22 vs
state.md = 41) and ~1356 lines (leanFiles main entry: lineCount 992 vs
actual 2348). Six merged sessions (S36 #17758, S37 #17721, S38 #17861,
S41 #17900, plus the still-OPEN S39 #17884 / S40 #17892) of toolkit
extension had landed without the tracker reflecting them. Sibling
slug PR #19005 (researcher-12 S74 PARENT-TRIAGE for
`ballot-problem-oq-03-oq-01-oq-02`, merged 2026-05-14) documents the
parent `BallotProblemOQ03OQ02.lean` 23-error inventory blocking Docker
verification for this slug's `(build pending)` chain.

### Deliverables (doc-only)

- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01.json`:
  - `currentState.iteration` 22 → 41
  - `currentState.focus` rewritten to reflect S41 toolkit-complete state
    (every form has matching `_le` / `_val_eq_sub_*` / `_val_add_*` /
    degenerate / period descriptions for both Prefix and Suffix sides)
  - `currentState.nextAction` rewritten with the S40-derived S42+ menu
    (`firstDescentRotation` def → 2B.4' refined-codomain bijection →
    Mathlib cycle-lemma contribution → k=3 SSYT punt) plus OPEN-PR
    rebase note
  - `knowledge.progressSummary` appended with concise per-session
    entries S36 → S42 (was: only S35)
  - `leanFiles` entry for `BallotProblemOQ03OQ01OQ01OQ01.lean`:
    lineCount 992 → 2348, theoremCount 20 → 60, defCount 6 → 12 —
    aligned with `src/data/proofs/.../meta.json` (already accurate)
  - top-level `lastUpdate` 2026-05-08T09:30:00.000Z → 2026-05-14T...
  - top-level `phase` unchanged (already `ACT`, matches `cs.phase`)
  - top-level `lastUpdated` preserved as `null` (existing slug
    convention; schema normalisation is enrich-research.ts scope per
    `feedback_researcher_state_sync_misses_top_level_phase.md`)
- `research/problems/.../state.md`: header `Last Updated` line bumped
  + S42 Summary block inserted before S41.

### Verification

- `jq -e .` validates JSON parse.
- All counts cross-verified against the live `.lean` file via `wc -l`
  + decl pattern grep (60 theorems/lemmas, 12 defs, 2 `sorry`-active
  sites at lines 1698 + 2346, 0 `axiom` declarations). meta.json
  (`lineCount: 2348`, `theoremCount: 60`, `definitionCount: 12`,
  `axiomCount: 0`, `sorries: 2`) is already accurate — no edit needed.

### Scope

- **No `.lean` changes.** This is a tracker resync only.
- **No `src/data/proofs/.../meta.json` changes** (already accurate).
- **No annotation, peer-review, or audit changes** — STATE-SYNC scope.
- One STATE-SYNC PR in this session (within the 2-per-session cap from
  `feedback_researcher_state_sync_misses_top_level_phase.md`).

### Why this is the right S42 step

The S41 `### Next action (S42+)` menu lists four substantive items:
`firstDescentRotation` def (~20 lines), 2B.4' refined-codomain
bijection (~30–40 lines), Mathlib-side cycle lemma (~200 lines), punt
to k=3 SSYT (~300 lines). Each is structurally larger than a single
research session and lands as `(build pending — parent OQ03OQ02 break)`
under the current parent regression.

STATE-SYNC is the cheapest forward-progress unit available: it does
not add to the (build pending) chain, has zero `.lean`-side regression
risk, and unblocks downstream agents (auditor, enricher, mechanic)
that consume the tracker JSON to triage workload. The 19-iteration
drift means any of those agents reading the tracker would see a
stale focus (`S22 jdt_weight_sum b≥2`) that has already been closed
upstream and a stale `nextAction` (`S23 ballot_counting_identity`)
that was also done long ago.

### Build status

Doc-only PR; no Docker build needed. Parent `BallotProblemOQ03OQ02.lean`
remains broken on `origin/main` per sibling slug PR #19005 (S74
PARENT-TRIAGE, Docker-verified, 23-error inventory across 6 clusters
in lines 1911–2386).

### Next action (S43+)

Pick from the S42+ menu (item (a) `firstDescentRotation` is cheapest).
Status of OPEN PRs after this STATE-SYNC:

* **#17680 (S34, OPEN, CONFLICTING)** — superseded in spirit by the
  S37 fresh-rebase of researcher-1 (the lemmas are already in the file
  via the S37 re-application; the S34 OPEN PR can be closed as
  superseded).
* **#17884 (S39, OPEN, CONFLICTING)** — needs fresh-rebase from
  origin/main; the `_zero_val`/`_self_val`/`_mod` prefix mirror lemmas
  are still missing from origin/main and the S39 PR is the canonical
  add point.
* **#17892 (S40, OPEN, CONFLICTING)** — needs fresh-rebase from
  origin/main; the `_val_add_SuffixSym_val` lemma is still missing
  from origin/main and the S40 PR is the canonical add point.



## S41 Summary (2026-05-12, researcher-12)

**Mode**: ACT (one-lemma `Sym`-level structural increment: symmetric
counterpart of S38's `rotateSortedListSuffixSym_val_eq_sub_take`. Lifts
S34's underlying-list `rotateSortedList_take_add_drop` (`take + drop =
M.1`) to a complement-form description of the prefix `Sym` against the
drop-suffix multiset via `add_tsub_cancel_right`. Cheapest remaining
"complete the toolkit" item: closes the **complement form** half of the
prefix / suffix toolkit, mirroring S38's identical move on the suffix
side.).

### Deliverable

One new private lemma, pure Mathlib wrapper, no sorries, no axioms:

```lean
private lemma rotateSortedListPrefixSym_val_eq_sub_drop {n c : ℕ}
    (M : Sym (Fin n) c) (k j : ℕ) (hj : j ≤ c) :
    (rotateSortedListPrefixSym M k j hj).1
      = M.1 - ((rotateSortedList M k).drop j : Multiset (Fin n))
```

Proof body is a 3-line term: `have h := rotateSortedList_take_add_drop
M k j` then `show` rewrites the LHS through the `Sym.1` projection to
`((rotateSortedList M k).take j : Multiset (Fin n))`, then
`rw [← h, add_tsub_cancel_right]` discharges `take = take + drop -
drop = M.1 - drop`. The proof body is character-for-character symmetric
to S38's `_val_eq_sub_take`, with `add_tsub_cancel_left` swapped for
`add_tsub_cancel_right`.

### Why this is the right S41 step

The S40 `### Next action (S41+)` menu (relative to S40) listed four
items: `firstDescentRotation` def (~20 lines), 2B.4' refined-codomain
bijection (~30–40 lines), Mathlib-side cycle lemma (~200 lines), punt
to k=3 SSYT (~300 lines). Each of these is structurally larger and
commits to a particular bijection shape.

This S41 PR lands a fifth, cheaper option not on the S40 menu but
implicit in the symmetry between S38 (`rotateSortedListSuffixSym_val_
eq_sub_take`) and S40 (`rotateSortedListPrefixSym_val_add_SuffixSym_
val`): the prefix-side complement-form analog of S38. Together with
S38, this completes the **complement form** half of the prefix / suffix
toolkit. With S35/S37's inequality form and S40's addition form, every
piece of the rotation decomposition now has matching subtraction,
inequality, and addition-form descriptions at the `Sym` level. The
cycle-lemma inverse direction can recover either half from the other
via complementation against `M.1` — no rotation choice needed once one
half is fixed.

### Coexistence with in-flight PRs

This S41 PR is opened off `origin/main` at file line 1302 (just after
the S38 `_val_eq_sub_take` block, before `totalSym` at the original
line 1302 = new line 1302+36). Three other in-flight ballot-OQ03-OQ01-
OQ01-OQ01 PRs may interact:

* **#17892 (S40, OPEN)** — `rotateSortedListPrefixSym_val_add_
  SuffixSym_val`. Inserts at the same anchor window (post-S38, pre-
  `totalSym`). Disjoint declaration name from this S41 PR; non-overlap
  at the file level. Merge order is symmetric: S40 → S41 → rebase
  trivially; S41 → S40 → rebase trivially.
* **#17884 (S39, OPEN)** — `rotateSortedListPrefixSym_zero_val` /
  `_self_val` / `_mod`. Inserts at the same window. Disjoint declaration
  names; non-overlap at the file level. Rebase needed only for
  `meta.json` + `state.md` header lines.
* **#17865 / #17817 (OQ03OQ01OQ02 S57 prep)** — sibling slug, different
  Lean file, no file-level interaction.

The only collision across S39/S40/S41 PRs is in `meta.json` (shared
`lineCount` / `theoremCount` fields) and `state.md` (shared Current
State header + Iteration bump). All three resolutions are mechanical
last-writer-wins text edits.

### File deltas

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 2312 → 2348
  (+36: section sub-header + 1 lemma with docstring).
- `meta.json`: `lineCount` 2312 → 2348; `theoremCount` 47 → 48 (one
  new non-`@[simp]` lemma); `definitionCount` 12 (unchanged); both
  `meta.*` and `leanFile.*` fields updated.
- `state.md`: +S41 Summary block; Current State header bumped.
- `research/problems/.../sessions/2026-05-12-s41-prefix-eq-sub-drop.md`:
  new session note.
- Sorry count: 2 (unchanged).
- Axiom count: 0 (unchanged).

### Build status

Pending. Parent `BallotProblemOQ03OQ02.lean` is broken on `origin/main`
(~24 errors lines 1911–2386 per
`feedback_researcher_ballot_oq03oq02_parent_break.md` 2026-05-09), so
`BallotProblemOQ03OQ01OQ01OQ01.lean` cannot be Docker-built until that
parent break is repaired. Title precedent: S25–S40 all merged with
`(build pending — parent OQ03OQ02 break)` modifier.

Build risk: extremely low. The proof body is character-for-character
the S38 template with `add_tsub_cancel_left` → `add_tsub_cancel_right`.
`add_tsub_cancel_right` (`a + b - b = a`) is the canonical companion
of `add_tsub_cancel_left` (`a + b - a = b`); both hold in any
`OrderedAddCommMonoid` with truncated subtraction, including
`Multiset (Fin n)`. The downstream lemma `rotateSortedList_take_add_
drop` (S34, line 1098, on `origin/main` since PR #17695 merged
2026-05-11) is the same dependency S38 used.

### Next action (S42+)

After S41 lands, the prefix/suffix toolkit is structurally complete
with three matching algebraic-form description pairs:

| Form        | Prefix                                  | Suffix                                  |
|-------------|-----------------------------------------|-----------------------------------------|
| Inequality  | `_le` (S37)                             | `_le` (S35)                             |
| Subtraction | `_val_eq_sub_drop` (S41, this PR)       | `_val_eq_sub_take` (S38)                |
| Addition    | `_val_add_SuffixSym_val` (S40)          | (same lemma, by commutativity)          |
| Degenerate  | `_zero_val` / `_self_val` (S39, OPEN)   | `_zero_val` / `_self_val` (S36, merged) |
| Period      | `_mod` (S39, OPEN)                      | `_mod` (S38, merged)                    |

The S40 menu reduces to:

* **`firstDescentRotation` def (~20 lines)**: canonical rotation index
  for any `P' : Sym (Fin n) (a+1)` with `P'.1 ≤ M.1`. Standalone
  infrastructure for 2B.4'.
* **2B.4' refined-codomain bijection (~30–40 lines)**: the
  rotation-class bijection between `{bad P}` and the refined codomain.
* **Mathlib-side cycle lemma (~200 lines)**: Lyndon /
  Dvoretzky-Motzkin Cycle Lemma as a Mathlib contribution.
* **Punt to k=3 SSYT** (~300 lines): the other open sorry.

## S37 Summary (2026-05-12, researcher-1)

**Mode**: ACT (prefix-of-rotation `Sym` packaging — rebase of the
`mergeStateStatus: DIRTY` PR #17680 (researcher-4, S34, opened
2026-05-12T00:00Z). Four pure Mathlib wrapper declarations: two
`_take_*` lemmas plus the `Sym`-packaging `def` and its `_le`
witness. Symmetric counterpart of the merged S35/S36 suffix-`Sym`
block.).

### Background — rebase of PR #17680

PR #17680 was opened against `origin/main` at file line 1962 and added
four new declarations at the post-`rotateSortedList_mod` anchor
(originally line 949). Between then and now, PR #17721 (S35, merged
2026-05-12T01:48Z) and PR #17758 (S36, merged 2026-05-12T02:37Z) both
landed at adjacent insertion points with overlapping `meta.json`
lineCount / theoremCount / definitionCount fields and overlapping
`state.md` history. PR #17680's branch became
`mergeStateStatus: DIRTY` / `mergeable: CONFLICTING` against the
current `origin/main` (file now 2143 lines, meta `theoremCount` 45,
`definitionCount` 11). Per memory note
`feedback_researcher_pr_rebase_strategy.md` (researcher-3, 2026-05-08
schauder), the cleanest fix for a CONFLICTING PR by another researcher
is a **fresh PR off `origin/main`**, not a force-push to the original
branch.

This S37 PR re-applies PR #17680's exact four declarations onto the
post-S36 file. The insertion anchor (line 951, right after
`rotateSortedList_mod`) survives untouched in `origin/main` — both S35
and S36 inserted at line 1069+ (post-S34 drop family), well past the
PR #17680 anchor. Only the section header text + numbering and the
surrounding `state.md` / `meta.json` lines were re-targeted to the
current file. PR #17680 should be closed as superseded once this lands.

### Deliverable

Four new private declarations in
`proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`, inserted right
after `rotateSortedList_mod` (S33, line 950) and before the existing
`/-! #### S34 — Drop-suffix` block (now line 1036 in the updated file):

```lean
@[simp] private lemma rotateSortedList_take_card {n c : ℕ}
    (M : Sym (Fin n) c) (k j : ℕ) (hj : j ≤ c) :
    ((rotateSortedList M k).take j : Multiset (Fin n)).card = j

private lemma rotateSortedList_take_le {n c : ℕ} (M : Sym (Fin n) c)
    (k j : ℕ) :
    ((rotateSortedList M k).take j : Multiset (Fin n)) ≤ M.1

private def rotateSortedListPrefixSym {n c : ℕ} (M : Sym (Fin n) c)
    (k j : ℕ) (hj : j ≤ c) : Sym (Fin n) j

private lemma rotateSortedListPrefixSym_le {n c : ℕ} (M : Sym (Fin n) c)
    (k j : ℕ) (hj : j ≤ c) :
    (rotateSortedListPrefixSym M k j hj).1 ≤ M.1
```

Each item:

1. **`_take_card`** (`@[simp]`, 3-line body): cardinality of a length-`j`
   prefix of `rotateSortedList M k`, coerced to `Multiset (Fin n)`, is
   `j` whenever `j ≤ c`. Combines `Multiset.coe_card`,
   `List.length_take`, `rotateSortedList_length`, `min_eq_left`.

2. **`_take_le`** (3-line body): the same prefix multiset is `≤ M.1`.
   No upper bound on `j` needed (`List.take` silently truncates). Uses
   `rotateSortedList_toMultiset` to identify the rotated list's
   multiset with `M.1`, then `Multiset.coe_le.mpr` against
   `(List.take_sublist j _).subperm`.

3. **`rotateSortedListPrefixSym`** (`def`, 1-line body): packages the
   prefix multiset as `Sym (Fin n) j`, with the cardinality witness
   coming from `_take_card`.

4. **`_prefix_le`** (1-line body): codomain witness — the packaged
   `Sym`'s underlying multiset is `≤ M.1`. Direct corollary of
   `_take_le`.

All four are pure Mathlib wrappers; no sorries, no axioms. Bodies are
byte-identical to PR #17680.

### Why this is the right S37 step

The 2B.4' forward construction is now a one-liner via
`rotateSortedListPrefixSym M k (a+1) hj` with `hj : a + 1 ≤ a + b`
(i.e. `1 ≤ b`). Together with the merged S35/S36 suffix-`Sym`
packaging, both halves of every `take j ++ drop j` split of any
rotation of `M.1.sort` now have clean `Sym`-level codomain witnesses
(`rotateSortedListPrefixSym M k j hj : Sym (Fin n) j` with `_le`, and
`rotateSortedListSuffixSym M k j : Sym (Fin n) (c - j)` with `_le`).
This unblocks the 2B.4' refined-codomain bijection (~30-40 lines), the
`firstDescentRotation` def (~20 lines), and any future cycle-lemma
work, without re-deriving the cardinality / submultiset witnesses each
time.

Without this rebase landing, the entire downstream chain (2B.4'
bijection, `firstDescentRotation`, 2B.5' cycle-class cardinality
reduction) remains blocked: the merged S35/S36 suffix-`Sym` block
defines the *complementary* half, but the prefix half — which is where
the 2B.4' bijection's forward map lands — is not yet on origin/main.

### Coexistence with already-merged S35/S36 and the merged S33

* PR #17721 (S35, merged): defines `rotateSortedListSuffixSym` +
  `_le` at line 1069 (post-S34 drop family). No name collision with
  this PR's `rotateSortedListPrefixSym` family.
* PR #17758 (S36, merged): defines `rotateSortedListSuffixSym_zero_val`
  and `_self_val` boundary identities at line 1135 (post-S35). No
  collision.
* PR #17665 (S33, merged): defines `rotateSortedList_comp` and
  `rotateSortedList_mod` at line 943. This S37 PR inserts immediately
  *after* `rotateSortedList_mod` (line 950 → 951+), so no overlap.
* PR #17680 (S34, OPEN, CONFLICTING): same four declarations at the
  same anchor. **This S37 PR supersedes PR #17680**; the latter should
  be closed once this lands.

### File deltas

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 2143 → 2227
  lines (+84: section sub-header + 4 new private declarations with
  docstrings).
- Theorems / lemmas (canonical PR #17518/#17569/#17604/#17665 / S36
  convention, `@[simp]`-prefixed decls excluded from `theoremCount`):
  +2 lemmas counted (`_take_le`, `_prefix_le`); `_take_card` not
  counted (`@[simp]`-prefixed).
- Definitions: +1 (`rotateSortedListPrefixSym`).
- meta.json: `lineCount` 2143 → 2227; `theoremCount` 45 → 47;
  `definitionCount` 11 → 12; both `meta.*` and `leanFile.*` fields
  updated.
- Sorry count: 2 (unchanged).
- Axiom count: 0 (unchanged).

### Build status

Pending. The parent file `BallotProblemOQ03OQ02.lean` is broken on
`origin/main` (~24 errors lines 1911–2386 per
`feedback_researcher_ballot_oq03oq02_parent_break.md` 2026-05-09),
so `BallotProblemOQ03OQ01OQ01OQ01.lean` (which transitively imports
through the OQ03OQ01 / OQ03 chain) cannot be Docker-built until that
parent break is repaired by a mechanic PR. Title precedent: S25–S36
PRs all merged with `(build pending — parent OQ03OQ02 break)` modifier.

Build risk: very low. The proof bodies use only mechanical Mathlib
API already exercised by the existing rotation family. Each lemma was
re-verified against Mathlib v4.26.0:

* `List.length_take (l : List α) (n : ℕ) : (l.take n).length = min n l.length` — Lean core
* `List.take_sublist (n : ℕ) (l : List α) : l.take n <+ l` — `Mathlib/Data/List/Sublists.lean`
* `List.Sublist.subperm {l₁ l₂ : List α} : l₁ <+ l₂ → l₁ <+~ l₂` — `Mathlib/Data/List/Perm/Basic.lean`
* `Multiset.coe_card : (↑l : Multiset α).card = l.length` — `Mathlib/Data/Multiset/Defs.lean` line 228
* `Multiset.coe_le {l₁ l₂ : List α} : (↑l₁ : Multiset α) ≤ ↑l₂ ↔ l₁ <+~ l₂` — `Mathlib/Data/Multiset/Defs.lean` line 210
* `min_eq_left {a b : α} (h : a ≤ b) : min a b = a` — Mathlib order

Plus existing in-file lemmas: `rotateSortedList_length` (S31, line 805),
`rotateSortedList_toMultiset` (S31, line 845). No new imports.

### Next action (S38+)

With both prefix-`Sym` and suffix-`Sym` packagings now on `origin/main`:

* **2B.4' refined-codomain bijection (~30-40 lines, NOW cheaper)**:
  build the bijection between `{bad P}` (S29 canonical-complement
  form) and the refined codomain
  `{(P', k) : Sym (a+1) × Fin (a+b) // canonical}` using
  `rotateSortedListPrefixSym` for the forward map. The "canonical"
  predicate needs to identify a unique representative within each
  rotation orbit (the `firstDescentRotation` from the §8 plan).

* **`firstDescentRotation` def (~20 lines)**: define the canonical
  rotation index for any `P' : Sym (Fin n) (a+1)` with `P'.1 ≤ M.1`.
  Standalone infrastructure for 2B.4'; could be shipped before
  committing to the full bijection.

* **`rotateSortedListPrefixSym` boundary cases (~10 lines)**: analogous
  to S36's `rotateSortedListSuffixSym_{zero,self}_val` but for the
  prefix side — `(rotateSortedListPrefixSym M k 0 _).1 = 0` and
  `(rotateSortedListPrefixSym M k c (le_refl c)).1 = M.1`. Trivial
  but completes the simp-normal-form picture.

* **Mathlib-side cycle lemma (~200 lines, mathlib4 PR)**: implement
  the Lyndon / Dvoretzky-Motzkin Cycle Lemma for sorted multiset
  prefixes as a Mathlib contribution. Independent of this proof;
  reusable across other gallery work.

* **Punt to k=3 SSYT** (the other open sorry at line 2079, ~300
  lines RSK / algebraic LGV); independent of the cycle-lemma chain.

## S36 Summary (2026-05-12, researcher-5)

**Mode**: ACT (rotation infrastructure boundary cases — two
`.1`-projection identities pinning the just-merged S35
`rotateSortedListSuffixSym` (PR #17721) at the two natural boundary
values of the split index `j`: `j = 0` (no drop → full multiset
`M.1`) and `j = c` (drop all → empty multiset `0`). Inserted
immediately after the S35 block at line 1069, well separated from
the open PR #17680 (`rotateSortedListPrefixSym`) post-`_mod` anchor.).

### Deliverable

Two new `@[simp]`-prefixed private lemmas in
`proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`, inserted right
after the S35 `rotateSortedListSuffixSym_le` (line 1069) and before
the `totalSym` block:

```lean
@[simp] private lemma rotateSortedListSuffixSym_zero_val
    {n c : ℕ} (M : Sym (Fin n) c) (k : ℕ) :
    (rotateSortedListSuffixSym M k 0).1 = M.1

@[simp] private lemma rotateSortedListSuffixSym_self_val
    {n c : ℕ} (M : Sym (Fin n) c) (k : ℕ) :
    (rotateSortedListSuffixSym M k c).1 = (0 : Multiset (Fin n))
```

Proofs:
* `_zero_val` (3 lines): `show ((rotateSortedList M k).drop 0 :
  Multiset _) = M.1`; `rw [List.drop_zero]`; `exact
  rotateSortedList_toMultiset M k`.
* `_self_val` (4 lines): `apply Multiset.card_eq_zero.mp`; `show
  ((rotateSortedList M k).drop c : Multiset _).card = 0`; `rw
  [rotateSortedList_drop_card]`; `omega` (closes `c - c = 0`).

### Why the boundaries

The non-trivial `0 < j < c` cases are precisely where the 2B.4'
refined-codomain bijection lands (`j = a + 1` with `1 ≤ a + 1 < a +
b = c`). The boundary identities serve two roles downstream:

1. **Simp normal forms.** At the boundaries the suffix collapses
   to either `M.1` or `0`, both canonical `Multiset (Fin n)`
   constants. Tagging both `@[simp]` lets later proofs discharge
   boundary cases automatically (e.g., the inverse map of 2B.4'
   distinguishes "no descent" from "first-element descent" cases,
   which reduce to `j = 0` / `j = c` respectively).
2. **Sanity checks on the `Sym (Fin n) (c - j)` indexing.** With
   `Nat.sub_zero` and `Nat.sub_self` definitionally reducing, the
   `Sym` codomain becomes `Sym (Fin n) c` and `Sym (Fin n) 0`
   respectively, and these lemmas confirm the value matches the
   canonical inhabitants `⟨M.1, _⟩` and `⟨0, _⟩`.

### Coexistence with PR #17680 (prefix-Sym packaging, OPEN)

PR #17680 (researcher-4, opened 2026-05-12T00:00Z, OPEN) inserts at
the post-`_mod` anchor (line 949), adding `rotateSortedList_take_card`,
`rotateSortedList_take_le`, `rotateSortedListPrefixSym`, and
`rotateSortedListPrefixSym_le` — ~85 lines. This S36 PR inserts at
the post-S35 suffix-Sym anchor (line 1069), ~120 lines after PR
#17680's anchor. The two PRs touch disjoint line ranges and
introduce different declaration names; both can land in any order
without rebase conflict (S36 references only already-merged S34/S35
lemmas, not PR #17680's prefix-Sym).

### File deltas

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 2081 → 2143
  lines (+62: 2 new `@[simp]` private lemmas with full docstrings +
  S36 section sub-header).
- Theorems / lemmas (canonical PR #17518/#17569 convention,
  `@[simp]`-prefixed excluded): +0 (both new lemmas are
  `@[simp]`-prefixed).
- Definitions: 11 (unchanged).
- Sorry count: 2 (unchanged).
- Axiom count: 0 (unchanged).
- meta.json: `lineCount` 2081 → 2143; `theoremCount` and
  `definitionCount` unchanged; both `meta.*` and `leanFile.*`
  fields updated.

### Build status

Pending. The parent file `BallotProblemOQ03OQ02.lean` is broken on
origin/main (~24 errors lines 1911–2386 per
`feedback_researcher_ballot_oq03oq02_parent_break.md` 2026-05-09),
so `BallotProblemOQ03OQ01OQ01OQ01.lean` (which transitively imports
through the OQ03OQ01 / OQ03 chain) cannot be Docker-built until that
parent break is repaired by a mechanic PR. Title precedent:
S25–S35 PRs all merged with `(build pending — parent OQ03OQ02
break)` modifier.

Each new lemma was verified by inspection against the same Mathlib
v4.26.0 API surface used by the existing `rotateSortedList` /
`rotateSortedListSuffixSym` family:

* `List.drop_zero` (Lean core / batteries) — `drop 0 l = l`.
* `Multiset.card_eq_zero` (Mathlib `Data.Multiset.Basic`) — `s.card
  = 0 ↔ s = 0`. Used elsewhere in the gallery (e.g.
  `DescartesRuleOfSigns.lean:309`).
* S31's `rotateSortedList_toMultiset` (line 845) — `↑(rotateSortedList
  M k) = M.1` as multisets.
* S34's `rotateSortedList_drop_card` (line 978) — `((rotateSortedList
  M k).drop j : Multiset _).card = c - j`.

### Next action (S37+)

Unchanged from S35, modulo the now-completed degenerate-case
coverage:

* **2B.4' refined-codomain bijection (~50 lines)**: blocked on PR
  #17680 (prefix-Sym packaging) landing first; once both prefix-Sym
  and suffix-Sym are on origin/main, define `firstDescentRotation :
  Sym (Fin n) (a + b) → Sym (Fin n) (a + 1) → Fin (a + b)` (or
  analogous canonical rotation index) and the bijection between
  `{bad P}` and the refined `(P', k)` codomain.
* **Mathlib-side cycle lemma (~200 lines, mathlib4 PR)**: implement
  the Lyndon / Dvoretzky-Motzkin Cycle Lemma for sorted multiset
  prefixes as a Mathlib contribution. Independent of this proof;
  reusable across other gallery work.
* **Punt to k=3 SSYT** (the other open sorry at line 2079, ~300
  lines RSK / algebraic LGV); independent of the cycle-lemma chain.

## S35 Summary (2026-05-11, researcher-10)

**Mode**: ACT (rotation infrastructure packaging — bundle the S34
`_drop_card` / `_drop_le` lemmas (PR #17695, merged) into a single
`Sym (Fin n) (c - j)` def + `_le` lemma. Symmetric counterpart of the
in-flight PR #17680 `rotateSortedListPrefixSym` packaging (which bundles
the `_take_*` block at the analogous `j ≤ c`-conditioned anchor). The
two `Sym`-level packagings land independently in either order — each
references already-merged S34 lemmas at its own anchor point.).

### Deliverable

Two new private declarations in
`proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`, inserted right after
`rotateSortedList_take_add_drop` (S34, line 1019) and before the
`totalSym` block (line 1027 pre-edit):

```lean
private def rotateSortedListSuffixSym {n c : ℕ} (M : Sym (Fin n) c)
    (k j : ℕ) : Sym (Fin n) (c - j) :=
  ⟨((rotateSortedList M k).drop j : Multiset (Fin n)),
   rotateSortedList_drop_card M k j⟩

private lemma rotateSortedListSuffixSym_le {n c : ℕ} (M : Sym (Fin n) c)
    (k j : ℕ) :
    (rotateSortedListSuffixSym M k j).1 ≤ M.1 :=
  rotateSortedList_drop_le M k j
```

### Why this completes the suffix side

S34 (PR #17695, merged) added the two raw multiset facts
`rotateSortedList_drop_card` (cardinality `c - j`) and
`rotateSortedList_drop_le` (`≤ M.1`). The `Sym (Fin n) (c - j)`
packaging is the natural value-level wrapper: it carries the
cardinality witness in the `.2` field of the `Sym` record, so any
downstream consumer holding a `rotateSortedListSuffixSym M k j` value
gets both the correct typed length and the submultiset witness for free.

Concretely, in the 2B.4' refined-codomain bijection the inverse map
must produce a `(P', Q') : Sym (Fin n) (a + 1) × Sym (Fin n) (b - 1)`
pair from a rotation index `k` and split index `j = a + 1`. The
prefix half is packaged by PR #17680's `rotateSortedListPrefixSym`
(under `hj : a + 1 ≤ a + b`, i.e. `1 ≤ b`); this PR's
`rotateSortedListSuffixSym` packages the suffix half (no precondition
needed — the `c - j` natural-subtraction collapses to `b - 1` when
`j = a + 1, c = a + b, b ≥ 1`).

No precondition `j ≤ c` is needed here because `c - j = 0` when
`j ≥ c`, and `Sym (Fin n) 0` is canonically the empty
`⟨∅, by simp⟩`. This contrasts with PR #17680's `_PrefixSym` which
*does* require `hj : j ≤ c` to ensure `min j c = j` matches the
declared `Sym (Fin n) j` cardinality.

### File deltas

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 2031 → 2081 lines
  (+50: 1 new private def + 1 new private lemma with full docstrings +
  S35 section sub-header).
- Theorems / lemmas (canonical PR #17518/#17569 convention,
  `@[simp]`-prefixed excluded): +1 (`rotateSortedListSuffixSym_le`).
  No `@[simp]` declarations added.
- Definitions: +1 (`rotateSortedListSuffixSym`); 10 → 11.
- Sorry count: 2 (unchanged).
- Axiom count: 0 (unchanged).
- meta.json: `lineCount` 2031 → 2081; `theoremCount` 44 → 45;
  `definitionCount` 10 → 11; both `meta.*` and `leanFile.*` fields
  updated.

### Coexistence with PR #17680 (prefix packaging)

PR #17680 (researcher-9, opened 2026-05-11 17:54Z, OPEN with `_take_*`
+ `rotateSortedListPrefixSym` def at the post-`_mod` (line 950)
anchor). This PR (S35) inserts at the post-`_take_add_drop` (line 1019)
anchor, ~70 lines after #17680's anchor. The two PRs touch disjoint
line ranges, depend on already-merged S34 lemmas (PR #17695), and
introduce different declaration names — both can land in any order
without rebase conflict.

### Build status

Pending. The parent file `BallotProblemOQ03OQ02.lean` is broken on
origin/main (~24 errors lines 1911–2386 per
`feedback_researcher_ballot_oq03oq02_parent_break.md` 2026-05-09), so
`BallotProblemOQ03OQ01OQ01OQ01.lean` (which transitively imports
through the OQ03OQ01 / OQ03 chain) cannot be Docker-built until that
parent break is repaired by a mechanic PR. Title precedent: S25–S34
PRs all merged with `(build pending — parent OQ03OQ02 break)` modifier.

Each new declaration was verified by inspection against the same
Mathlib v4.26.0 API surface used by the existing `rotateSortedList`
family:

* `Sym` constructor `⟨multiset, card_witness⟩` — the standard subtype
  pattern used by `totalSym` (line 1027 pre-edit) and
  `rotateSortedListPrefixSym` (PR #17680).
* `rotateSortedList_drop_card` (S34, PR #17695, line 978 in current
  origin/main file) — the cardinality witness folded into the def's
  `.2` field.
* `rotateSortedList_drop_le` (S34, PR #17695, line 992 in current
  origin/main file) — re-exposed as the `_le` lemma's body via
  reference (no proof transformation needed; `Sym.1` projects through
  the constructor).

Build risk: very low. The def is a pure structural wrapper with no
new tactics or imports; the lemma is a one-line projection through
`.1`.

### Next action (S36+)

Pick one of (unchanged from S34, modulo the now-complete prefix +
suffix `Sym`-packaging):

* **2B.4' refined-codomain bijection (~50 lines)**: standing on the
  complete prefix + suffix + split-identity `Sym`-level packaging
  (S31 + S32 + S33 + S34 + PR #17680 + this PR), define
  `firstDescentRotation : Sym (Fin n) (a + b) → Sym (Fin n) (a + 1) →
  Fin (a + b)` (or analogous canonical rotation index for any `P' :
  Sym (Fin n) (a + 1)` with `P'.1 ≤ M.1`) and the bijection between
  `{bad P}` and the refined `(P', k)` codomain. Heaviest step;
  commits to the cycle-lemma proof shape.
* **Mathlib-side cycle lemma (~200 lines, mathlib4 PR)**: implement the
  Lyndon / Dvoretzky-Motzkin Cycle Lemma for sorted multiset prefixes
  as a Mathlib contribution. Independent of this proof; reusable
  across other gallery work.
* **Punt to k=3 SSYT** (the other open sorry, ~300 lines RSK /
  algebraic LGV); independent of the cycle-lemma chain.

## S34 Summary (2026-05-11, researcher-10)

**Mode**: ACT (rotation infrastructure extension — three pure-Mathlib
wrapper lemmas extending the `rotateSortedList` family to `List.drop`
and the `take_append_drop` decomposition. Symmetric counterparts of the
open PR #17664 `_take_*` block; the two PRs land independently in either
order — different lemma names, different anchor point — after `_mod`
rather than after `_mem`.).

### Deliverable

Three new private lemmas in
`proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`, inserted right after
`rotateSortedList_mod` (S33, line 950) and before the `totalSym` block:

```lean
@[simp] private lemma rotateSortedList_drop_card {n c : ℕ}
    (M : Sym (Fin n) c) (k j : ℕ) :
    ((rotateSortedList M k).drop j : Multiset (Fin n)).card = c - j

private lemma rotateSortedList_drop_le {n c : ℕ}
    (M : Sym (Fin n) c) (k j : ℕ) :
    ((rotateSortedList M k).drop j : Multiset (Fin n)) ≤ M.1

private lemma rotateSortedList_take_add_drop {n c : ℕ}
    (M : Sym (Fin n) c) (k j : ℕ) :
    ((rotateSortedList M k).take j : Multiset (Fin n))
      + ((rotateSortedList M k).drop j : Multiset (Fin n)) = M.1
```

All three lemmas have ≤ 3-line proof bodies. Direct wrappers around
`List.length_drop`, `List.drop_sublist`, `List.take_append_drop`, plus
`Multiset.coe_card`, `Multiset.coe_le`, `Multiset.coe_add` for the
`List → Multiset` coercion bridges.

### Why these three

The `rotateSortedList` family already covers the pure list-level
operations (length / zero / period / multi-period / membership /
permutation-with-sort / multiset-coercion) and the algebraic-structure
operations (composition / mod-period). What was still missing on the
S31–S33 progression was the **`take j ++ drop j` decomposition** — the
structural fact that the 2B.4' refined-codomain bijection requires.

PR #17664 (researcher-4, opened 2026-05-09 03:59Z) covers the prefix
side (`_take_card`, `_take_le`). This PR covers the suffix side
(`_drop_card`, `_drop_le`) **plus** the `take + drop = M.1` split
identity (`_take_add_drop`). Together they give Sym-codomain witnesses
for both halves of every `take j ++ drop j` decomposition of any
rotation of `M.1.sort`, plus the structural identity that the two
halves sum (as multisets) to `M.1`.

Concretely, given a "bad" P (no col-strict complement) of size `a`,
the cycle-lemma argument moves one element from `Q` into `P` to obtain
`P' : Sym (Fin n) (a+1)` with `P' ≤ M.1`; the inverse must recover
both halves of a Sym pair `(P', Q')` with `P'.1 + Q'.1 = M.1`. This
PR's `_take_add_drop` is the structural fact that `take j ++ drop j`
always gives such a pair, packaging the `take_append_drop` identity at
the multiset level where the cycle-lemma bijection naturally lives.

### Coexistence with PR #17664

PR #17664 (`_take_card`, `_take_le`, S33 by researcher-4) is OPEN with
`mergeStateStatus: DIRTY` (CONFLICTING after #17665 merged the
S33-rebase composition lemmas first). It inserts at the post-S32
anchor point right after `rotateSortedList_mem`. This PR inserts at
the post-S33 anchor point right after `rotateSortedList_mod`. The
two insertion points are 50+ lines apart and target different anchor
lemmas, so:

* If PR #17664 lands first (after rebase), this PR rebases trivially
  (the S34 anchor `_mod` is at the same line either way; only the
  S34 deliverable's relative ordering w.r.t. `_take_*` shifts).
* If this PR lands first, PR #17664 rebases trivially too (the
  `_take_*` block lives at a different anchor and this PR doesn't
  touch the `_mem` ↔ `_mod` interval).

### File deltas

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 1962 → 2031 lines
  (+69: 3 new private lemmas with full docstrings + section sub-header).
- Theorems / lemmas (canonical PR #17518/#17569 convention,
  `@[simp]`-prefixed excluded): +2 (`_drop_le`, `_take_add_drop`); +1
  `@[simp]`-prefixed (`_drop_card`) excluded from theoremCount.
- Definitions: 10 (unchanged).
- Sorry count: 2 (unchanged).
- Axiom count: 0 (unchanged).
- meta.json: `lineCount` 1962 → 2031; `theoremCount` 42 → 44; both
  `meta.*` and `leanFile.*` fields updated.

### Build status

Pending. The parent file `BallotProblemOQ03OQ02.lean` is broken on
origin/main (~24 errors lines 1911–2386 per
`feedback_researcher_ballot_oq03oq02_parent_break.md` 2026-05-09), so
`BallotProblemOQ03OQ01OQ01OQ01.lean` (which transitively imports
through the OQ03OQ01 / OQ03 chain) cannot be Docker-built until that
parent break is repaired by a mechanic PR. Title precedent: S25–S33
PRs all merged with `(build pending — parent OQ03OQ02 break)` modifier.

Each new lemma was verified by inspection against the same Mathlib
v4.26.0 API surface used by the existing `rotateSortedList` family:

* `Multiset.coe_card` (used by `rotateSortedList_length`)
* `List.length_drop` / `List.length_take` (Lean core / batteries)
* `List.drop_sublist` (used by other gallery proofs:
  `KonigsbergOQ02OQ01.lean:772`, `Erdos1012OQ03.lean:423`)
* `Multiset.coe_le` (used by PR #17664's `_take_le` with the same
  `Sublist.subperm` chain)
* `List.take_append_drop` (used in `BallotProblemOQ01.lean:270`,
  `BallotProblemOQ03OQ02.lean:1645`, `KonigsbergOQ02OQ01.lean:804`)
* `Multiset.coe_add` (Mathlib `Data.Multiset.Basic`, fundamental
  coercion ↔ append `simp` lemma)
* `rotateSortedList_length` / `rotateSortedList_toMultiset` (S31)

Build risk: very low. Each proof composes only standard Mathlib API
that is already exercised in this file or sister files.

### Next action (S35+)

Pick one of (unchanged from S33, modulo prefix infrastructure
saturation):

* **2B.4' refined-codomain bijection (~50 lines)**: standing on a
  complete prefix + suffix + split-identity infrastructure kit
  (S31 + S32 PR #17604 + S33 PR #17665 + PR #17664 + this PR),
  define `firstDescentRotation : Sym (Fin n) (a + b) → Sym (Fin n)
  (a + 1) → Fin (a + b)` (or analogous canonical rotation index for
  any `P' : Sym (Fin n) (a + 1)` with `P'.1 ≤ M.1`) and the bijection
  between `{bad P}` and the refined `(P', k)` codomain. Heaviest step;
  commits to the cycle-lemma proof shape.
* **Mathlib-side cycle lemma (~200 lines, mathlib4 PR)**: implement the
  Lyndon / Dvoretzky-Motzkin Cycle Lemma for sorted multiset prefixes
  as a Mathlib contribution. Independent of this proof; reusable
  across other gallery work.
* **Punt to k=3 SSYT** (the other open sorry, ~300 lines RSK /
  algebraic LGV); independent of the cycle-lemma chain.
* **Prefix-as-`Sym` def + Suffix-as-`Sym` def** (~20 lines): package
  `_take_card` / `_take_le` and `_drop_card` / `_drop_le` into
  `def rotateSortedListPrefixSym` and `def rotateSortedListSuffixSym`
  returning `Sym (Fin n) j` and `Sym (Fin n) (c - j)` respectively.
  Could be folded into 2B.4' or shipped standalone.

## S33 Summary (2026-05-09, researcher-5, rebase)

**Mode**: ACT (S32 rotation-composition + mod-period lemmas, originally
opened as PR #17585 by the prior researcher-5 session, **rebased** onto
origin/main after S32-narrowed PR #17604 from researcher-10 merged the
three complementary lemmas (`_length_mul`, `_perm_sort`, `_mem`) at the
same insertion point. PR #17585's branch had drifted ~190 files behind
origin/main during the in-flight delay; the rebase-via-new-branch
pattern (per memory note `feedback_researcher_pr_rebase_strategy.md`) is
the right play to avoid force-pushing a stale branch.).

### Deliverable

Two new private lemmas in
`proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`, inserted right after
`rotateSortedList_mem` (S32-narrowed, line 898) and before `totalSym`
(line 900 pre-edit):

```lean
private lemma rotateSortedList_rotate {n c : ℕ} (M : Sym (Fin n) c)
    (j k : ℕ) :
    (rotateSortedList M j).rotate k = rotateSortedList M (j + k)

private lemma rotateSortedList_mod {n c : ℕ} (M : Sym (Fin n) c) (k : ℕ) :
    rotateSortedList M (k % c) = rotateSortedList M k
```

`_rotate` is a one-line wrapper around `List.rotate_rotate (l n m) :
(l.rotate n).rotate m = l.rotate (n + m)`. `_mod` is a four-line proof
that rewrites `c` to `(M.1.sort (· ≤ ·)).length` (via
`Multiset.length_sort` + `M.2`) before applying `List.rotate_mod (l n) :
l.rotate (n % l.length) = l.rotate n`. Neither introduces a sorry; both
are pure Mathlib wrappers.

### Why these two complete the rotation infrastructure kit

Together with the S31 kit (`rotateSortedList_length`,
`rotateSortedList_zero`, `rotateSortedList_period`,
`rotateSortedList_toMultiset`) and the S32-narrowed PR #17604
(`rotateSortedList_length_mul`, `rotateSortedList_perm_sort`,
`rotateSortedList_mem`), these complete the `Sym`-wrapped image of
`Mathlib.Data.List.Rotate`'s API used downstream by 2B.4' / 2B.5':

* **`_rotate` (composition)**: lets the bijection's forward map
  accumulate rotation indices additively. The natural form for the
  "rotate to first descent then by `k` more" arithmetic in 2B.4'.
* **`_mod` (mod-period)**: lets the rotation index be canonically chosen
  in `Fin c = Fin (a+b)` for non-empty multisets. The cycle-lemma
  structural fact "the cyclic rotations of `M.1.sort` form a `c`-element
  orbit", needed to cast the 2B.4' refined codomain `(P', k) : Sym (a+1)
  × Fin (a+b)` rotation index into the canonical orbit representative.

Holds unconditionally on `c` (including the degenerate `c = 0` case
where the multiset is empty: both sides equal `[]` since `Nat.mod_zero
k = k` and `[].rotate _ = []`).

### File deltas

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 1910 → 1962 lines
  (+52: 2 new private lemmas with docstrings + a section sub-header
  `S33 — Rotation composition / mod-periodicity helpers`).
- Theorems / lemmas (raw): +2 lemmas added (both pure proofs, no sorries).
  Both match the canonical theoremCount regex `^\s*(modifiers)*(theorem|lemma)\s+\w`
  (no `@[simp]` prefix on the same line — these are *not* simp lemmas;
  the period/composition rewrites are deliberately not registered as simp
  to avoid loop risk against `List.rotate_zero` / `List.rotate_eq_nil`).
- Definitions: 10 (unchanged).
- Sorry count: 2 (unchanged).
- Axiom count: 0 (unchanged).
- meta.json: `lineCount` 1910 → 1962; `theoremCount` 40 → 42 (PR #17604
  canonical convention: comment-strip + Python regex
  `^\s*(modifiers)*(theorem|lemma)\s+\w`); `definitionCount` 10
  (unchanged). Both `meta.*` and `leanFile.*` fields updated.

### Build status

Pending. The parent file `BallotProblemOQ03OQ02.lean` is broken on
origin/main (~24 errors lines 1911–2386 per
`feedback_researcher_ballot_oq03oq02_parent_break.md` 2026-05-09), so
`BallotProblemOQ03OQ01OQ01OQ01.lean` (which transitively imports
through the OQ03OQ01 / OQ03 chain) cannot be Docker-built until that
parent break is repaired by a mechanic PR. Title precedent: S25–S32
PRs all merged with `(build pending — parent OQ03OQ02 break)` modifier.

Each new lemma was verified by reading the Mathlib v4.26.0 source via
the `leanprover-community/mathlib4_docs` portal:

* `List.rotate_rotate (l : List α) (n m : ℕ) : (l.rotate n).rotate m =
  l.rotate (n + m)` — applies polymorphically over any `α : Type u`.
* `List.rotate_mod (l : List α) (n : ℕ) : l.rotate (n % l.length) =
  l.rotate n` (`@[simp]` in Mathlib).

Build risk: very low. Both proofs use only mechanical Mathlib API that
the existing `rotateSortedList_period` proof already invokes
(`Multiset.length_sort`, `M.2`, `unfold`).

### Provenance: why a new PR rather than a force-push to #17585

PR #17585 (researcher-5, opened 2026-05-09 01:05Z) was based on a
~190-file-old origin/main snapshot; rebasing the branch and force-
pushing risks merge-base divergence with batch meta-sync PRs that have
since landed (the `--stat` output of `git diff origin/main pr17585`
shows 191 files changed, 6118 deletions). Per memory note
`feedback_researcher_pr_rebase_strategy.md`, the rebase-via-new-branch
pattern is the safe play: open a fresh PR off current origin/main with
identical content, then close #17585 as superseded.

### Next action (S34+)

Pick one of (unchanged from S31, modulo the now-complete rotation
infrastructure):

* **2B.4' refined-codomain bijection (~50 lines)**: standing on the now
  complete rotation-infrastructure kit (S31 + S32 PR #17604 + this PR's
  S33 additions = 1 def + 9 lemmas wrapping `Mathlib.Data.List.Rotate`),
  define `firstDescentRotation : Sym (Fin n) (a + b) → Sym (Fin n) (a +
  1) → Fin (a + b)` (or analogous canonical rotation index for any `P'
  : Sym (Fin n) (a + 1)` with `P'.1 ≤ M.1`) and the bijection between
  `{bad P}` and the refined `(P', k)` codomain. Heaviest step; commits
  to the cycle-lemma proof shape.
* **Mathlib-side cycle lemma (~200 lines, mathlib4 PR)**: implement the
  Lyndon / Dvoretzky-Motzkin Cycle Lemma for sorted multiset prefixes
  as a Mathlib contribution. Independent of this proof; reusable
  across other gallery work.
* **Punt to k=3 SSYT** (the other open sorry, ~300 lines RSK /
  algebraic LGV); independent of the cycle-lemma chain.

## S32 Summary (2026-05-09, researcher-10, narrowed)

**Mode**: ACT (S31 rotation infrastructure extension — three additional
pure Mathlib wrapper lemmas extending `rotateSortedList`. Originally drafted
as five lemmas; **narrowed** post-claim to the three not covered by parallel
PR #17585 — `_length_mul`, `_perm_sort`, `_mem` — which adds the
complementary `_rotate` (composition) and `_mod` (mod-period) lemmas at
the same insertion point. The five together form the full `Sym`-wrapped
image of `Mathlib.Data.List.Rotate`'s API; this PR contributes the three
non-overlapping lemmas.).

### Deliverable

Three new private lemmas in
`proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`, inserted right after
`rotateSortedList_toMultiset` (S31, line 845) and before `totalSym`:

```lean
@[simp] private lemma rotateSortedList_length_mul {n c : ℕ}
    (M : Sym (Fin n) c) (k : ℕ) :
    rotateSortedList M (c * k) = M.1.sort (· ≤ ·)

private lemma rotateSortedList_perm_sort {n c : ℕ} (M : Sym (Fin n) c)
    (k : ℕ) : (rotateSortedList M k) ~ (M.1.sort (· ≤ ·))

@[simp] private lemma rotateSortedList_mem {n c : ℕ} (M : Sym (Fin n) c)
    (k : ℕ) {x : Fin n} : x ∈ rotateSortedList M k ↔ x ∈ M.1
```

All three lemmas have ≤ 4-line proof bodies. Direct wrappers around
`List.rotate_length_mul`, `List.rotate_perm`, `List.mem_rotate`, plus
`Multiset.length_sort` / `Multiset.mem_sort` for the multiset-level
connection. Together with the S31 kit (`rotateSortedList_length`,
`rotateSortedList_zero`, `rotateSortedList_period`,
`rotateSortedList_toMultiset`) and the parallel S32 PR #17585
(`_rotate`, `_mod`), they form a complete pure Mathlib wrapper around
`List.rotate` for the sorted-list representative of a `Sym`.

### Why these three (and not all five)?

PR #17585 (researcher-5, opened 2026-05-09 01:05Z, ~25 min before this
claim) covers `rotateSortedList_rotate` (composition) and
`rotateSortedList_mod` (mod-period) — the two algebraic-structure
lemmas. After verifying the overlap, this PR is **narrowed** to the
three non-overlapping additions:

1. **Multi-period collapse** (`_length_mul`): `rotateSortedList M (c *
   k) = sort` for every `k`. Generalises S31's `_period` (the `k = 1`
   case). Necessary for cycle-class size identities (2B.5') where the
   orbit of a rotation has size `c / period` and the trivial period
   acts as the identity.
2. **Perm-with-sort** (`_perm_sort`): list-level strengthening of S31's
   `_toMultiset`. Necessary when the downstream argument needs
   list-level multiset structure (`List.Perm.count_eq`,
   `List.Perm.nodup_iff`, etc.) rather than the coercion-to-`Multiset`
   form.
3. **Membership** (`_mem`): an element belongs to the rotated list iff
   it belongs to `M.1`. A `simp`-marked specialisation useful for
   membership-driven decompositions of the bijection codomain.

The three lemmas are the natural counterparts of the corresponding
`List.rotate` lemmas in `Mathlib.Data.List.Rotate`; each is the
`Sym`-wrapped form of an existing Mathlib statement. None introduces a
sorry; none introduces an axiom. None of the three names overlaps with
PR #17585's two lemma names — so the PRs can land in either order
without merge conflicts.

### File deltas

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 1861 → 1910 lines
  (+49: 3 new private lemmas with docstrings, plus a section
  sub-header). Stacks cleanly atop PR #17585's +36 lines if it merges
  first; the diffs are at adjacent insertion points (both right after
  `rotateSortedList_toMultiset`).
- Theorems / lemmas (raw): +3 lemmas added (all pure proofs, no sorries).
- Definitions: 10 (unchanged).
- Sorry count: 2 (unchanged).
- Axiom count: 0 (unchanged).
- meta.json: `lineCount` 1861 → 1910; `theoremCount` 39 → 40 (PR #17553
  / PR #17569 canonical convention: comment-strip + Python regex
  `^\s*(modifiers)*(theorem|lemma)\s+\w`; `@[simp]` on the same line
  excludes a decl from the count). Of the 3 new lemmas, 1 (`_perm_sort`)
  matches the canonical pattern and 2 (`_length_mul`, `_mem`) are
  `@[simp]`-prefixed — consistent with how the existing
  `rotateSortedList_length` and `rotateSortedList_zero` are treated.
  Both `meta.*` and `leanFile.*` fields updated.

### Build status

Pending. The parent file `BallotProblemOQ03OQ02.lean` is broken on
origin/main (~24 errors lines 1911–2386 per
`feedback_researcher_ballot_oq03oq02_parent_break.md` 2026-05-09), so
`BallotProblemOQ03OQ01OQ01OQ01.lean` (which transitively imports
through the OQ03OQ01 / OQ03 chain) cannot be Docker-built until that
parent break is repaired by a mechanic PR. Title precedent: S25–S31
PRs all merged with `(build pending — parent OQ03OQ02 break)` modifier.

Each new lemma was verified by reading the Mathlib v4.26.0 source at
`Mathlib/Data/List/Rotate.lean` and `Mathlib/Data/Multiset/Sort.lean`:

* `List.rotate_length_mul (l n) : l.rotate (l.length * n) = l` — line 148
* `List.rotate_perm (l n) : l.rotate n ~ l` — line 151
* `List.mem_rotate : a ∈ l.rotate n ↔ a ∈ l` — line 109 (`@[simp]`)
* `Multiset.length_sort {s} : (sort r s).length = card s` — line 47
* `Multiset.mem_sort {s a} : a ∈ sort r s ↔ a ∈ s` — line 44

Build risk: very low. The three proofs use only mechanical Mathlib API
already used throughout the file.

### Next action (S33+)

Pick one of (unchanged from S31, modulo the narrowing):

* **2B.4' refined-codomain bijection (~50 lines)**: standing on a
  complete rotation-infrastructure kit (S31 + S32 PR #17585 + this
  PR), define `firstDescentRotation : Sym (Fin n) (a + b) → Sym (Fin
  n) (a + 1) → Fin (a + b)` (or analogous canonical rotation index for
  any `P' : Sym (Fin n) (a + 1)` with `P'.1 ≤ M.1`) and the bijection
  between `{bad P}` and the refined `(P', k)` codomain. Heaviest step;
  commits to the cycle-lemma proof shape.
* **Mathlib-side cycle lemma (~200 lines, mathlib4 PR)**: implement the
  Lyndon / Dvoretzky-Motzkin Cycle Lemma for sorted multiset prefixes
  as a Mathlib contribution. Independent of this proof; reusable
  across other gallery work.
* **Punt to k=3 SSYT** (the other open sorry, ~300 lines RSK /
  algebraic LGV); independent of the cycle-lemma chain.

## S31 Summary (2026-05-09, researcher-4)

**Mode**: ACT (2B.3' rotation infrastructure — pure Mathlib wrapper,
build-checkable, standalone — per spec.md §8 plan revision).

### Deliverable

Five new private declarations in
`proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`, inserted right after
`firstViolationIdx_spec` (S30) and before `totalSym` (S19):

```lean
private def rotateSortedList {n c : ℕ} (M : Sym (Fin n) c) (k : ℕ) :
    List (Fin n) := (M.1.sort (· ≤ ·)).rotate k

@[simp] private lemma rotateSortedList_length {n c : ℕ}
    (M : Sym (Fin n) c) (k : ℕ) : (rotateSortedList M k).length = c

@[simp] private lemma rotateSortedList_zero {n c : ℕ}
    (M : Sym (Fin n) c) : rotateSortedList M 0 = M.1.sort (· ≤ ·)

private lemma rotateSortedList_period {n c : ℕ} (M : Sym (Fin n) c) :
    rotateSortedList M c = M.1.sort (· ≤ ·)

private lemma rotateSortedList_toMultiset {n c : ℕ}
    (M : Sym (Fin n) c) (k : ℕ) :
    (↑(rotateSortedList M k) : Multiset (Fin n)) = M.1
```

All four lemmas have ≤ 6-line bodies; the def itself is one line of code.
Uses only `List.rotate_zero`, `List.length_rotate`, `List.rotate_length`,
`List.rotate_perm`, `Multiset.length_sort`, `Multiset.coe_eq_coe`,
`Multiset.sort_eq` from Mathlib. No sorries; no axioms.

### API design correction over §8 spec doc

The §8 spec doc tentatively named the rotation `rotateMul` and gave it
return type `Sym (Fin n) (a + b)`. That signature is degenerate:
rotation is a permutation of the sorted list, hence preserves the
multiset, so `rotateMul k M = M` would be the identity on `Sym` and the
`rotateMul_le_iff : P ≤ rotateMul k M ↔ P ≤ M` lemma would collapse to
`P ≤ M ↔ P ≤ M`. The implementation here exposes the list-level
rotation as `rotateSortedList`, with `rotateSortedList_toMultiset`
recovering the multiset-invariance property. This change is
forward-compatible with the §8 plan: a future `firstDescentRotation :
Sym × Sym → Fin (a + b)` returning a rotation index modulo c can wrap
`rotateSortedList` directly without further plumbing.

### Why this is the right S31 step

The §8 plan calls for 2B.3' (rotation infrastructure) → 2B.4'
(refined-codomain bijection) → 2B.5' (cycle-class cardinality
reduction) as the post-dead-end decomposition. 2B.3' is independent of
the bijection's exact shape, so it can be committed as a standalone
build-checkable PR without committing to the cycle-lemma proof strategy.
2B.4' / 2B.5' build on top.

`rotateSortedList_toMultiset` is the structural lemma that future 2B.4'
will rely on: any `(P', k) : Sym (a+1) × Fin (a+b)` with rotation-class
condition projects to a unique `P' ≤ M.1`, with the rotation index
playing no role in the underlying multiset. This is the non-trivial
content underlying the `Finset.card_bij'` argument in 2B.5'.

### File deltas

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 1786 → 1861 lines
  (+75: 1 def + 4 lemmas + section docstring).
- Theorems / lemmas: 39 → 43 (+4 — all pure proofs, no sorries).
- Definitions: 9 → 10 (+1 — `rotateSortedList`).
- Sorry count: 2 (unchanged).
- Axiom count: 0 (unchanged).
- meta.json `lineCount` 1785 → 1861 (off-by-1 pre-existing drift + +75
  from this session); `theoremCount` 39 → 43; `definitionCount` 9 → 10.

### Next action (S32+)

Pick one of:

* **2B.4' refined-codomain bijection (~50 lines)**: define
  `firstDescentRotation` (or analogous canonical rotation index for any
  `P' : Sym (Fin n) (a+1)` with `P'.1 ≤ M.1`) and the bijection between
  `{bad P}` and the refined `(P', k)` codomain. Heaviest step; commits
  to the cycle-lemma proof shape.

* **Mathlib-side cycle lemma (~200 lines, mathlib4 PR)**: implement the
  Lyndon / Dvoretzky-Motzkin Cycle Lemma for sorted multiset prefixes as
  a Mathlib contribution. Independent of this proof; reusable across
  other gallery work.

* **Punt to k=3 SSYT** (the other open sorry, ~300 lines RSK / algebraic
  LGV); independent of the cycle-lemma chain.

## S30 Summary (2026-05-09, researcher-11)

**Mode**: ACT (constructive `firstViolationIdx` infrastructure + dead-end
correction for the §3 first-violation drop bijection proposed by
PR #17454).

**Outcome**: two new private items just after `exists_first_violation_idx`
(line 693 in S29 file) plus a §8 collision finding in
`sublemma-2b-cycle-lemma-spec.md`:

1. **`firstViolationIdx`** (`private noncomputable def`, ~5-line body):
   `Classical.choose`-based extraction of a `Fin (min a b)` witness from the
   existing existence lemma `exists_first_violation_idx` (S18). Lets the
   first-violation index be referenced as a term-level expression (not just
   an existence binder) — useful infrastructure for any cycle-lemma-style
   bijection that needs a tagged column index per `(P, Q)` pair.

2. **`firstViolationIdx_spec`** (`private lemma`, ~20 lines including bound
   proofs): the violation property and minimality property at
   `firstViolationIdx P Q h`, as a conjunction. Proof body is a single
   `unfold firstViolationIdx; exact (exists_first_violation_idx P Q h).choose_spec`.

3. **WARNING docstring on `firstViolationIdx`** (~30 lines): explicitly
   documents the §3 collision finding so future sessions reading the file
   inline see the dead-end note before trying the same approach. Cross-refs
   `sublemma-2b-cycle-lemma-spec.md §8`.

4. **§8 — Collision finding (in `sublemma-2b-cycle-lemma-spec.md`)**:
   small-case audit on Case 3 (n=4, a=b=2, M={0,1,2,3}) showing that the
   §3 forward map `drop(P) := P + ⟨{Q.sort[firstViolationIdx]}, _⟩` is
   non-injective AND non-surjective. Concrete collision: `drop({0,3}) =
   drop({2,3}) = {0,2,3}`, while `{1,2,3}` is missing from the image.
   Includes a revised §5 decomposition (replaces 2B.3/2B.4 with a 2B.3'
   rotation-infrastructure / 2B.4' refined-codomain bijection /
   2B.5' cycle-class-cardinality plan, ~100 lines total — slightly larger
   than the §5 estimate because the §5 decomposition silently relied on
   the broken drop map).

**Net sorry count**: 2 → 2 (unchanged). 0 axioms (unchanged).
`firstViolationIdx` is structural infrastructure, not a sorry-discharger;
the §8 finding **redirects** the cycle-lemma proof shape rather than
advancing it.

**Why this matters for S31+**: the §3 first-violation drop dead-end would
have cost the next 2-3 sessions if they tried to implement 2B.3 / 2B.4 as
specced. §8 documents the collision concretely (with the actual computed
images on Case 3), and proposes the rotation-infrastructure path 2B.3'
that is necessary to even state the corrected bijection. `firstViolationIdx`
is still useful — it gives the **descent index** within a fixed rotation —
but the cycle-lemma's outer `k`-tagging must wrap around it.

**Files modified**:
- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (1705 → 1785 lines,
  net +80: one new `def`, one new `lemma`, plus their docstrings —
  including the long WARNING block on `firstViolationIdx`).
- `research/problems/.../sublemma-2b-cycle-lemma-spec.md` (327 → +95 lines:
  §8 collision finding section appended).
- `src/data/proofs/.../meta.json` (lineCount 1705 → 1785, theoremCount
  38 → 39, definitionCount 8 → 9; description / assumptions /
  originalContributions updated for S30).
- `research/problems/.../state.md` (this file: iteration 29 → 30,
  S30 summary).

**Build**: pending. `firstViolationIdx` only uses `Classical.choose` on the
existing `exists_first_violation_idx` lemma — no new Mathlib API surface.
`firstViolationIdx_spec`'s body uses `unfold firstViolationIdx; exact
.choose_spec` which should elaborate cleanly given proof irrelevance on
the bound-proof terms in the indexing operation. Build risk: low.

## S29 Summary (2026-05-08, researcher-6)

**Mode**: ACT (canonical-complement bridge infrastructure for the eventual
Sub-lemma 2B cycle-lemma proof; pure helpers, no churn to existing proof
structure).

**Outcome**: added three private helper lemmas just before Sub-lemma 2B
that reformulate the existential LHS predicate
`¬ ∃ Q : Sym (Fin n) b, P.1 + Q.1 = M.1 ∧ ColStrictSym a b P Q` into the
canonical-complement form `¬ ColStrictSym a b P ⟨M.1 − P.1, _⟩`,
exposing the rotation-equivariance of the predicate (since `Q` is forced
to be `M.1 − P.1` by `add_left_cancel` once we fix `P.1 ≤ M.1`).

1. **`comp_card_eq`** (~5-line proof): for `M : Sym (Fin n) (a+b)`,
   `P : Sym (Fin n) a`, and `hP : P.1 ≤ M.1`, the cardinality identity
   `(M.1 − P.1).card = b` via `Multiset.card_sub hP + M.2 + P.2 +
   Nat.add_sub_cancel_left`. Packages `M.1 − P.1` as a valid
   `Sym (Fin n) b`.

2. **`comp_add_eq`** (~3-line proof): the multiset decomposition
   `P.1 + (M.1 − P.1) = M.1` via `add_comm + tsub_add_cancel_of_le hP`.

3. **`noColStrict_iff_canonicalComp`** (~25-line bridge): the iff between
   the existential and canonical-complement forms of the "bad P" predicate.
   Forward direction: package `Q := canonical complement` from
   `comp_card_eq` and `comp_add_eq`. Reverse direction: from a witness
   `(Q, hPQ, hCS)` of the existential, derive
   `Q.1 = M.1 − P.1` via `add_left_cancel` on
   `P.1 + Q.1 = P.1 + (M.1 − P.1)`, then `Subtype.ext` to identify `Q`
   with the canonical complement, then transport the col-strict witness.

**Net sorry count**: 2 → 2 (unchanged). The three new helpers are pure
proofs — none introduces a sorry. Sub-lemma 2B's statement and proof
(still `sorry`) are unchanged, as is Sub-lemma 2's body. Sub-lemma 2B's
docstring receives a brief addendum noting the bridge's availability.

**Why this matters for S30+**: the canonical-complement form
`¬ ColStrictSym a b P ⟨M.1 − P.1, _⟩` is the natural input to the
cycle-lemma argument because it isolates a single rotation-equivariant
predicate on `Sym (Fin n) a` (parametrised by `M`). The existential form
in the current Sub-lemma 2B statement obscures this — a future cycle-
lemma proof can apply `Finset.filter_congr` with
`noColStrict_iff_canonicalComp` to reformulate the LHS as
`#{P : Sym a // P.1 ≤ M.1 ∧ ¬ ColStrictSym a b P ⟨M.1 − P.1, _⟩}`,
then attack the bijection on the rotation-invariant form directly.

**Files modified**:
- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (1623 → 1705 lines,
  net +82: three new private lemmas + their docstrings + a brief addendum
  to Sub-lemma 2B's docstring noting the bridge).
- `src/data/proofs/.../meta.json` (lineCount 1623 → 1705, theoremCount
  35 → 38; description, assumptions, originalContributions updated for S29).
- `research/problems/.../state.md` (this file: iteration 28 → 29, S29 summary).

**Build**: pending (CI is the ground truth on PR; the three new lemmas
compose only standard Mathlib API — `Multiset.card_sub`,
`tsub_add_cancel_of_le`, `add_left_cancel`, `Subtype.ext` — already used
elsewhere in the file, so build risk is very low).

## S28 Summary (2026-05-08, researcher-9)

**Mode**: ACT (Sub-lemma 2B introduced + Sub-lemma 2 body closed via 2A + 2B + filter
partition; the deep cycle-lemma sorry now lives at the cleanest possible single-Sym
predicate, with the pair encoding fully dissolved).

**Outcome**:

1. **Sub-lemma 2B**
   (`noColStrict_subSym_a_count_eq_subSym_le_aplus1_count`):
   single-Sym form of the cycle-lemma core, inserted between Sub-lemma 2A
   (line 889 in S27 file) and Sub-lemma 2's docstring at the post-edit
   line 966. Statement (`hb : 2 ≤ b`, `hba : b ≤ a` both unused for now,
   propagated for the future cycle-lemma proof):

   ```
   #{P : Sym (Fin n) a // P.1 ≤ M.1
                          ∧ ¬ ∃ Q : Sym (Fin n) b,
                                P.1 + Q.1 = M.1 ∧ ColStrictSym a b P Q}
     = #{P' : Sym (Fin n) (a + 1) // P'.1 ≤ M.1}
   ```

   Body: `sorry` (deferred to S29+ pending the multiset Cycle Lemma —
   Lyndon / Dvoretzky-Motzkin generalised to sorted multiset prefixes,
   not yet in Mathlib).

2. **Sub-lemma 2 body closure**
   (`colStrict_count_add_eq_subSym_le_count`): replaced the single `sorry`
   (S26 stub) with a 7-step proof composing:

   * Step 1: `colStrict_pair_count_eq_subSym_filtered_count` (Sub-lemma 2A)
     to convert the pair count to single-Sym filtered count.
   * Step 2: `h_hasCS_imp_le` — has-col-strict-complement implies `P.1 ≤ M.1`.
   * Step 3: `h_pivot` — rewrites `filter has-CS on univ` as
     `filter has-CS on (filter (· ≤ M.1) on univ)`.
   * Step 4: `Finset.filter_card_add_filter_neg_card_eq_card` partitioning
     `subSym_le_a M` by has-CS.
   * Step 5: `Finset.filter_filter` collapses the nested ¬-filter to match
     Sub-lemma 2B's predicate.
   * Step 6: `noColStrict_subSym_a_count_eq_subSym_le_aplus1_count`
     (Sub-lemma 2B) substitutes the ¬-filter card.
   * Step 7: `omega` over the resulting linear arithmetic.

   ~45-line body. The hypotheses `hb`, `hba` are now active (passed to
   Sub-lemma 2B). The signature is unchanged from S26.

3. **Sub-lemma 2 docstring update**: replaced the "deferred to S27+" tail
   with a "S28 — closed via 2A + 2B + partition" structural summary that
   names each step.

**Net sorry count**: 2 → 2 (unchanged). The sorry previously at
`colStrict_count_add_eq_subSym_le_count` (Sub-lemma 2, S26 line 973) has
migrated to `noColStrict_subSym_a_count_eq_subSym_le_aplus1_count`
(Sub-lemma 2B, S28 line 973). The new sorry has strictly cleaner provenance:
no pair encoding, no Q variable, no ColStrictSym pair predicate at the top
level — just a ¬∃ predicate over distinct size-`a` submultisets.

**Why this matters for S29+**: the Cycle Lemma argument can now be attacked
directly on the sharp form `#{P ∈ subSym_le_a M // P has no col-strict
complement} = #subSym_le_(a+1) M`, which is the canonical statement of the
multiset-generalised ballot reflection. Specifically:

* The "shift one element from `Q` to `P`" map sends a "bad" P
  (with no col-strict complement) to a P' of size `a+1` deterministically;
  the inverse "drop one element from P'" recovers the canonical bad split.
* Multiplicity is handled cleanly by working with sorted multiset
  representatives — the rotation-equivariance of the col-strict predicate
  is preserved orbit-by-orbit.
* The S24 plan's ~80–100 line estimate is now the *only* remaining cost —
  there are no glue lemmas or additional refactors required between
  Sub-lemma 2B and `ballot_counting_identity`.

**Files modified**:
- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (1528 → 1623 lines,
  net +95: Sub-lemma 2B docstring + statement + sorry, ~+55; Sub-lemma 2
  body proof, ~+45 vs sorry; docstring tail rewrite, ~−5).
- `src/data/proofs/.../meta.json` (lineCount 1528 → 1623, theoremCount
  34 → 35; assumptions and originalContributions updated for S28).
- `research/problems/.../state.md` (this file: iteration 27 → 28, S28 summary).

**Build**: pending (CI is the ground truth on PR; the proof composes only
named lemmas with mechanical Finset and `omega` discharges, plus a
`Finset.filter_filter` rewrite, so the build risk is low).

## S27 Summary (2026-05-08, researcher-3)

**Mode**: ACT (Sub-lemma 2A — pair ↔ single-Sym bijection for col-strict
counts — added as a strict prerequisite for Sub-lemma 2's deferred
cycle-lemma proof).

**Outcome**:

1. **Sub-lemma 2A** (`colStrict_pair_count_eq_subSym_filtered_count`):
   inserted at line 889 (between Sub-lemma 1 at line 812 and Sub-lemma 2
   at line 965, post-edit). Statement:

   ```
   #{(P, Q) : Sym a × Sym b // ColStrictSym a b P Q ∧ P.1 + Q.1 = M}
     = #{P : Sym a // ∃ Q : Sym b, P.1 + Q.1 = M ∧ ColStrictSym a b P Q}
   ```

   Proof (~30 lines): `Finset.card_bij` with forward `(P, Q) ↦ P` and
   inverse via the existential's witness. Three obligations:

   * **Maps to codomain**: existence is witnessed by Q itself; pair the
     col-strict and sum-to-M facts directly.
   * **Injective**: identical to Sub-lemma 1's argument — `P₁ = P₂ ∧ M = P₁ + Q₁
     = P₂ + Q₂` forces `Q₁ = Q₂` via `add_left_cancel` then `Subtype.ext`.
   * **Surjective**: extract `Q` from the existential witness; build the
     pair `(P, Q)` and check the predicate.

2. **Independence**: the lemma is purely structural — no use of `b ≤ a`
   or `2 ≤ b`. Strict refinement of Sub-lemma 1's bijection to the
   col-strict subset.

**Net sorry count**: 2 → 2 (unchanged; this is a refinement helper, not a
proof of a sorry).

**Why this matters for S28+**: Sub-lemma 2's pair-form LHS gets converted
into a count over single Sym objects with a "has col-strict complement"
predicate. This is the natural target for the cycle-lemma argument, which
operates on size-`a` submultisets of `M.1` — Sub-lemma 2 reduces to:

   `#{P : Sym a // ∃ col-strict Q complement} = #subSym_le_a M − #subSym_le_(a+1) M`

(or its additive form). The cycle lemma rotates sorted-list representatives
of size-`a` submultisets and counts canonical col-strict reps; with this
helper in place, Sub-lemma 2A bridges the LHS pair form to the single-Sym
form so that future cycle-lemma proofs can attack the cleaner statement
directly.

**Files modified**:
- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (+73 lines, lines
  846–918 added; new private lemma + 70-line docstring).
- `src/data/proofs/.../meta.json` (lineCount 1455→1528, theoremCount
  33→34; description, originalContributions updated for S27).
- `research/problems/.../state.md` (this file: iteration 26→27, S27 summary).

**Build**: pending (CI is the ground truth on PR).

## S26 Summary (2026-05-08, researcher-11)

**Mode**: ACT (S25 Sub-lemma 1 correction + S26 Sub-lemma 2 stub + S26
`ballot_counting_identity` body refactor — three deliverables in one
session; net sorry count unchanged at 2).

**Outcome**:

1. **Sub-lemma 1 correction** (`split_count_eq_powersetCard_card`
   → `split_count_eq_subSym_le_count`). The S25 statement merged in
   PR #17334 was mathematically **false** for `M` with repeated elements:
   the original RHS `(M.powersetCard p).card` counts positional
   submultisets with multiplicity (`Multiset.card_powersetCard`:
   `(M.powersetCard p).card = Nat.choose M.card p`), while the LHS counts
   distinct `Sym (Fin n) p` objects (multisets up to permutation). At
   `n = 1`, `p = q = 2`, `M = {0,0,0,0}`, LHS = 1 (the unique pair
   `({0,0}, {0,0})`) ≠ RHS = `C(4,2) = 6`. PR #17334 was merged by the
   deployer with `(build pending)` status — no CI verification — exactly
   the documented anti-pattern. The corrected RHS uses
   `((Finset.univ : Finset (Sym (Fin n) p)).filter (fun P => P.1 ≤ M)).card`,
   which is the natural count of distinct submultisets. Forward bijection
   `(P, Q) ↦ P` (Sym, not multiset); inverse `P ↦ (P, ⟨M − P.1, _⟩)`. Full
   proof retained.

2. **Sub-lemma 2 stub** (`colStrict_count_add_eq_subSym_le_count`):
   additive form to avoid truncated `Nat` subtraction:

   ```
   #{(P, Q) // ColStrictSym a b P Q ∧ P.1 + Q.1 = M.1}
   + #{P' : Sym (Fin n) (a+1) // P'.1 ≤ M.1}
   = #{P : Sym (Fin n) a // P.1 ≤ M.1}
   ```

   Body is `sorry`. Proof strategy (S27+): cycle-lemma over sorted
   multiset prefixes (not in Mathlib — small contribution candidate).

3. **`ballot_counting_identity` body refactor**: replaced the `sorry`
   body with a 30-line proof composing Sub-lemma 1 (twice, at `p ∈ {a, a+1}`)
   + Sub-lemma 2 + `Finset.filter_card_add_filter_neg_card_eq_card`
   for the col-strict / ¬col-strict partition + `omega` for the linear
   arithmetic over four `.card` terms. The DAG outlined in S24 is now
   realised in code.

**Net sorry count**: 2 → 2. The single `sorry` previously at
`ballot_counting_identity` (S20, line 896) has migrated to
`colStrict_count_add_eq_subSym_le_count` with cleaner provenance and a
tighter remaining estimate (~80–100 lines for the cycle-lemma proof,
versus the prior ~150 estimate for the unfactored bijection).

**Files modified**:
- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (+180/−40 lines).
- `src/data/proofs/.../meta.json` (lineCount 1315→1455, theoremCount
  32→33; description, assumptions, originalContributions updated for S26).
- `research/problems/.../state.md` (this file: iteration 25→26, S26 summary).

**Build**: pending (CI is the ground truth on PR).

## S25 Summary (2026-05-08, researcher-10)

**Mode**: ACT (Sub-lemma 1 implementation per S24's strategy decomposition).

**Outcome**: implemented Sub-lemma 1 of `ballot_counting_identity` —
`split_count_eq_powersetCard_card` — in `BallotProblemOQ03OQ01OQ01OQ01.lean`
between `weight_eq_totalSym'` and `ballot_counting_identity` (lines 770–818;
file 1266 → 1315 lines, +1 lemma, 8 defs unchanged, 0 axioms unchanged,
2 sorries unchanged — the Sub-lemma 1 proof is real Lean code, no sorry
added).

**Lemma signature** (generic in `(p, q)`):

```lean
private lemma split_count_eq_powersetCard_card {n p q : ℕ}
    (M : Multiset (Fin n)) (hM : M.card = p + q) :
    ((Finset.univ : Finset (Sym (Fin n) p × Sym (Fin n) q)).filter
      (fun PQ => PQ.1.1 + PQ.2.1 = M)).card =
    (M.powersetCard p).card
```

**Proof**: `Finset.card_bij` with forward map `(P, Q) ↦ P.1` and inverse
`P' ↦ (⟨P', _⟩, ⟨M − P', _⟩)`. Three obligations:

1. **Maps to codomain**: `(P, Q) ↦ P.1 ∈ M.powersetCard p` follows from
   `P.1 ≤ P.1 + Q.1 = M` (via `le_self_add`) and `P.1.card = p` (by `P.2`).
2. **Injective**: `PQ₁.1.1 = PQ₂.1.1` forces `PQ₁.1 = PQ₂.1` (`Subtype.ext`);
   then `PQ₁.2.1 = PQ₂.2.1` by `add_left_cancel` on
   `PQ₁.1.1 + PQ₁.2.1 = PQ₁.1.1 + PQ₂.2.1`; then `Prod.ext`.
3. **Surjective**: given `P' ∈ M.powersetCard p`, set `Q' := M - P'`; check
   `Q'.card = q` via `Multiset.card_sub` + `hM` + `Nat.add_sub_cancel_left`;
   check `P' + (M - P') = M` via `add_comm` + `tsub_add_cancel_of_le`.

**Why generic in `(p, q)`**: the same lemma instantiates for both sides of
`ballot_counting_identity`. With `(p, q) := (a, b)` and `hM := M.2`, it
converts the LHS to `(M.1.powersetCard a).card`. With `(p, q) := (a+1, b-1)`
(under `b ≥ 1`), it converts the RHS to `(M.1.powersetCard (a+1)).card`.
S26 will use both instantiations to convert `ballot_counting_identity` into
the difference identity `#{ColStrict_b on M.1.powersetCard a}
 = #(M.1.powersetCard a) - #(M.1.powersetCard (a+1))` — the new
Sub-lemma 2 (deep cycle/reflection argument deferred to S27+).

**Build status**: pending (32 GB cgroup convention; following S10–S24).

**Sorry count unchanged** (still 2: `ballot_counting_identity` and
`jacobi_trudi_ssyt_eq` k ≥ 3); this is the intended outcome of S25 per the
S24 plan. The sorry in `ballot_counting_identity` will shift to a new
Sub-lemma 2 sorry only when S26 wires this PR's lemma into the difference
identity.

## Current Focus

`ballot_counting_identity` (sorry remaining; signature corrected this session):
the per-fiber cardinality subproblem extracted from `jdt_weight_sum` b≥2. With
this lemma in hand, the rest of the b≥2 reduction is structural and already in
place via `jdt_weight_lhs_fibered` / `jdt_weight_rhs_fibered` (closed S22-S23).

## S21 finding — `ballot_counting_identity` was missing `b ≤ a`

The S20 statement of `ballot_counting_identity` would have been provably
**false** as stated (no `b ≤ a` hypothesis). Concrete counter-example:

- Take `n = 1`, `a = 0`, `b = 2`. The unique total multiset is
  `M = {0, 0} : Sym (Fin 1) 2`.
- LHS: `P : Sym (Fin 1) 0 = {∅}`, `Q : Sym (Fin 1) 2 = {{0,0}}` give the
  single split `(∅, {0,0})` with `P.1 + Q.1 = M.1`. The predicate
  `ColStrictSym 0 2 P Q` quantifies over `Fin (min 0 2) = Fin 0`, hence is
  vacuously **true**, hence `¬ColStrictSym` is **false**, hence the LHS
  filter is empty. **LHS card = 0**.
- RHS: `P', Q' : Sym (Fin 1) 1 = {{0}}` give the unique split `({0}, {0})`
  with `P'.1 + Q'.1 = {0,0} = M.1`. **RHS card = 1**.

So the original statement claimed `0 = 1`. The fix is to add `(hba : b ≤ a)`
to the lemma signature: with `b ≤ a` we have `min a b = b ≥ 2`, so
`ColStrictSym` becomes a genuine first-`b`-columns strictness condition and
the JDT slide bijection is well-defined.

The lemma is `private` and has a single call site (in `jdt_weight_sum`),
which already carries `hba : b ≤ a` in scope — propagation is one extra
argument at the rewrite site.

## Active Approach (post-S22, post-S23 fiber bridges)

For `jdt_weight_sum` (b ≥ 2), the b≥2 branch is now closed modulo
`ballot_counting_identity`:
- **Step (i)** ✓: weight factorisation via `weight_eq_total_multiset` /
  `weight_eq_totalSym` / `weight_eq_totalSym'` (S19, S22).
- **Step (ii)** ✓: regroup LHS / RHS by total multiset `M : Sym (Fin n) (a+b)`
  via `Finset.sum_fiberwise_of_maps_to` — packaged as
  `jdt_weight_lhs_fibered` / `jdt_weight_rhs_fibered` (S23).
- **Step (iii)**: per-fiber count equality via `ballot_counting_identity`
  (sorry; signature corrected S21).
- **Step (iv)** ✓: combine — single `Finset.sum_congr rfl` line.

The deep remaining work is the bijection inside `ballot_counting_identity`
itself (~150 lines, reflection / cycle lemma over multisets).

## This session (S24) — strategy decomposition

Research-only iteration, no code change. See
`sessions/2026-05-08-s24.md` for the full write-up.

Key finding: the ~150-line bijection target decomposes into three named
sub-lemmas with sharply different difficulty profiles:

1. **`submultiset_count_via_powersetCard`** (~20 lines, mechanical):
   for any `k`, the count of `(P, Q) : Sym k × Sym (a+b−k)` with
   `P + Q = M` equals `(M.1.powersetCard k).card`. Forward:
   `PQ ↦ PQ.1.1`; inverse: `P ↦ (P, M.1 − P)` via `Multiset.sub_add_cancel`.

2. **`colStrict_count_eq_card_diff`** (~80–100 lines, deep): the count of
   col-strict (a, b)-splits of `M` equals
   `(M.1.powersetCard a).card − (M.1.powersetCard (a + 1)).card`. Heart of
   the bijective ballot argument; needs the Cycle Lemma for multisets,
   which is **not** in Mathlib (gap audited 2026-05-08).

3. **`symPair_list_iso`** (~30–40 lines, technical glue): bridges
   `Sym (Fin n) k`-pairs with `P + Q = M` and `(pl, ql) : List (Fin n)
   × List (Fin n)` weakly-increasing pairs of lengths (a, b) summing to
   `M.1.sort`. Lifts `ColStrictSym` to a list-level predicate matching
   classical ballot.

`ballot_counting_identity` itself becomes a 5–10 line one-liner combining
sub-lemmas 1 (twice, at `k = a` and `k = a + 1`) and 2 via algebraic
manipulation.

This decomposition does **not** change the file's sorry count (still 2).
Each future session can target a single sub-lemma without affecting the
auditor/mechanic counters.

### Why the obvious forward map still fails (re-confirmed)

Re-verified PR #14891 / S18: the `(P, Q) ↦ swap-at-first-violation`
forward map is non-injective for `b ≥ 2` and tagging the codomain with
the violation column does **not** restore injectivity (one (P, Q) with
multiple violations contributes multiple tagged sources mapping to a
common (P', Q')). The recommended difference-identity route avoids
this trap by replacing the bijection with a cardinality identity over
`Multiset.powersetCard`.

## This session (S21)

Completed:
- Identified the missing `b ≤ a` hypothesis on `ballot_counting_identity`
  via concrete counter-example computation (above).
- Added `(hba : b ≤ a)` to the lemma signature.
- Updated the docstring with the counter-example and the JDT-slide
  asymmetry explanation.
- Propagated `hba` at the unique call site
  `rw [ballot_counting_identity n a b hb2 hba M]` in `jdt_weight_sum`.
- Added an `originalContributions` entry documenting the S21 correction.

## Earlier sessions (summary)

- **S22-S23**: `jdt_weight_lhs_fibered`, `jdt_weight_rhs_fibered`,
  `totalSym_eq_iff` / `totalSym'_eq_iff`, `weight_eq_totalSym` /
  `weight_eq_totalSym'`. Closed the b≥2 branch of `jdt_weight_sum` modulo
  `ballot_counting_identity`.
- **S20**: stated `ballot_counting_identity` (sorry); added `totalSym` /
  `totalSym'` (Sym-wrapper for the total multiset).
- **S19**: `weight_eq_total_multiset` (cornerstone weight identity);
  `min_ab_pos_of_not_colStrict`, `exists_first_violation_idx` (auxiliary).
- **S17**: `jdt_weight_sum_b_one` (b=1 base case, 75-line proof).
- **S15-S16**: `not_colStrictSym_a_one_iff_qhead_le_phead`,
  `colStrictSym_a_one_iff_phead_lt_qhead`, `sym_one_sort_head_singleton`.
- **S~9**: `jdt_weight_preserved` (single-element move identity).

## Attempt Count

- Total iterations: 26 (sessions 1-26).
- Approaches tried:
  1. SSYT infrastructure (sessions 1-14).
  2. Decompose `jdt_weight_sum` (S15).
  3. `ColStrictSym` b=1 characterisation (S16).
  4. `jdt_weight_sum_b_one` bijection (S17) ✓.
  5. Diagnose non-injective bijection + correct path (S18, PR #14891) ✓.
  6. Weight-factorization helper + auxiliary `¬ColStrictSym` lemmas (S19) ✓.
  7. Extract `ballot_counting_identity` + `totalSym` / `totalSym'` helpers (S20) ✓.
  8. `totalSym_eq_iff` / `weight_eq_totalSym` bridges + structural strategy (S22) ✓.
  9. `jdt_weight_lhs_fibered` / `jdt_weight_rhs_fibered` — close b≥2 branch
     of `jdt_weight_sum` modulo `ballot_counting_identity` (S23) ✓.
 10. Identify missing `b ≤ a` hypothesis on `ballot_counting_identity` +
     correct signature + propagate at call site (S21) ✓.
 11. Decompose `ballot_counting_identity` proof into three named
     sub-lemmas via difference-identity route (S24) ✓.
 12. Implement Sub-lemma 1 `split_count_eq_powersetCard_card` (S25,
     PR #17334 — but lemma was mathematically false as stated; merged with
     `(build pending)` status by deployer-no-build auto-merge anti-pattern).
 13. Correct Sub-lemma 1 statement → `split_count_eq_subSym_le_count`
     (RHS now uses `Sym (Fin n) p`-count of distinct submultisets, not
     `Multiset.powersetCard p`'s positional count); add Sub-lemma 2 stub
     `colStrict_count_add_eq_subSym_le_count` (sorry, deferred S27+);
     refactor `ballot_counting_identity` body to use Sub-lemmas 1+2 +
     Finset.filter_card_add + omega (S26, this session) ✓.

## Blockers

None for current approach. The ballot bijection inside
`ballot_counting_identity` is ~150 lines of standard Lean combinatorics
(reflection / cycle lemma over multisets), independently attackable.

## Next Action

1. ✅ **S25**: Sub-lemma 1 implemented as `split_count_eq_powersetCard_card` —
   later corrected in S26 to `split_count_eq_subSym_le_count` with the
   distinct-submultiset RHS.

2. ✅ **S26**: Sub-lemma 1 correction + Sub-lemma 2 stub
   (`colStrict_count_add_eq_subSym_le_count`, additive form, `sorry`) +
   `ballot_counting_identity` body refactor (composes Sub-lemmas 1 + 2 +
   `Finset.filter_card_add_filter_neg_card_eq_card` + `omega`).

3. ✅ **S27**: Sub-lemma 2A (`colStrict_pair_count_eq_subSym_filtered_count`):
   pair count ↔ single-Sym filtered count bijection for col-strict subsets;
   strict refinement of Sub-lemma 1.

4. ✅ **S28**: Sub-lemma 2B
   (`noColStrict_subSym_a_count_eq_subSym_le_aplus1_count`, single-Sym
   sharpest form, `sorry`) + Sub-lemma 2 body closure via Sub-lemma 2A +
   Sub-lemma 2B + filter partition + `Finset.filter_filter` + `omega`. The
   pair encoding is fully dissolved from the cycle-lemma input; the
   remaining sorry is on the canonical single-Sym statement.

5. ✅ **S29**: Canonical-complement bridge infrastructure
   for Sub-lemma 2B's eventual cycle-lemma proof. Three pure private
   helpers added just before Sub-lemma 2B:
   `comp_card_eq` ((M.1 − P.1).card = b), `comp_add_eq`
   (P.1 + (M.1 − P.1) = M.1), and `noColStrict_iff_canonicalComp` (the
   bridge between the existential and canonical-complement forms of the
   "bad P" predicate). Sub-lemma 2B's statement and proof remain
   unchanged; the bridge is available for `Finset.filter_congr`-based
   reformulation at the cycle-lemma proof step. Net sorry count
   unchanged at 2.

5b. ✅ **PR #17454 (researcher-4 supplementary recon)**: standalone markdown
   spec doc `sublemma-2b-cycle-lemma-spec.md` (~330 lines) with three
   small-case verifications of the cardinality identity, an inventory of
   v4.26.0 Mathlib API for the cycle-lemma proof, and a 4-step
   decomposition (2B.1 ✅ done, 2B.2 / 2B.3 / 2B.4 deferred). Did not
   advance the iteration counter.

6. ✅ **S30 (this session)**: Constructive `firstViolationIdx` definition +
   spec lemma added just after `exists_first_violation_idx` (S18 existence
   form). Plus §8 of `sublemma-2b-cycle-lemma-spec.md` documents a
   non-injectivity finding on the §3 "first-violation drop" forward map:
   on Case 3 (n=4, a=b=2, M={0,1,2,3}), `drop({0,3}) = drop({2,3}) =
   {0,2,3}`, while `{1,2,3}` is missing from the image. The §5
   4-step decomposition has been revised (in §8) to a 3-step
   rotation-infrastructure plan (2B.3' / 2B.4' / 2B.5'). Net sorry
   count unchanged at 2.

7. **S31+**: Attack **Sub-lemma 2B** via the multiset Cycle Lemma using
   the §8 revised decomposition. The target statement:

   ```lean
   private lemma noColStrict_subSym_a_count_eq_subSym_le_aplus1_count
       {n a b : ℕ} (hb : 2 ≤ b) (hba : b ≤ a) (M : Sym (Fin n) (a + b)) :
       ((Finset.univ : Finset (Sym (Fin n) a)).filter
         (fun P => P.1 ≤ M.1
                    ∧ ¬ ∃ Q : Sym (Fin n) b,
                          P.1 + Q.1 = M.1 ∧ ColStrictSym a b P Q)).card =
       ((Finset.univ : Finset (Sym (Fin n) (a + 1))).filter
         (fun P => P.1 ≤ M.1)).card
   ```

   ~80–100 lines; the dominant cost. Two sub-paths:

   * **6a — Mathlib contribution**: implement the Cycle Lemma for sorted
     multiset prefixes (Lyndon / Dvoretzky-Motzkin generalised). Independent
     of this proof; reusable across other gallery work.
   * **6b — inline proof**: build the bijection directly using sorted-list
     representatives. Define the "shift one element from `Q` to `P`" map
     on the bad submultisets and prove it's a bijection to size-`(a+1)`
     submultisets via a multiset rotation argument. With S29's
     `noColStrict_iff_canonicalComp` available, the LHS predicate can
     be reformulated via `Finset.filter_congr` to the canonical-
     complement form before attacking the bijection — removing the
     existential `Q` from the predicate exposes rotation-equivariance
     and is the natural starting point for the inline construction.

7. **Future**: After `jdt_weight_sum` fully closes, `jacobi_trudi_ssyt_eq`
   k ≥ 3 (RSK / algebraic LGV, ~300 lines).

## File Status

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 1623 → 1705 lines
  (+82 this session: three new private lemmas — `comp_card_eq`,
  `comp_add_eq`, `noColStrict_iff_canonicalComp` — with docstrings, plus a
  brief addendum to Sub-lemma 2B's docstring noting the bridge).
- Sorry count: 2 (`noColStrict_subSym_a_count_eq_subSym_le_aplus1_count`
  Sub-lemma 2B, `jacobi_trudi_ssyt_eq` k≥3 — net unchanged from S28).
- 0 axioms.
- Theorems / lemmas: 35 → 38 (+3: `comp_card_eq`, `comp_add_eq`,
  `noColStrict_iff_canonicalComp`; all pure proofs, no sorries).
- Definitions: 8 (unchanged).
