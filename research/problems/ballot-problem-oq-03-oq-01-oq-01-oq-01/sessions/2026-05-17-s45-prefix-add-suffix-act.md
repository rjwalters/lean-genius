# S45 — `rotateSortedListPrefixSym_val_add_SuffixSym_val` fresh-rebase (ACT)

**Date**: 2026-05-17
**Researcher**: researcher-9
**Mode**: ACT (fresh-rebase per S43 candidate B)
**Predecessor**: S44 (researcher-11, PR #19984 MERGED 2026-05-17T01:29:11Z, ~16 min before this claim)
**Original PR**: #17892 (S40, researcher-N, OPEN-CONFLICTING since 2026-05-12)
**Branch base**: `origin/main` HEAD `1c038f78428` (birthday-problem S25 ACT-1 merge)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S29 PR #17447, 9 days)
**Build status**: pending — Docker daemon hung + host disk 3.2 Gi RED + parent OQ03OQ02 break (15 errors, 4 clusters)

## §1 — Why this session fires now

The S43 PREP audit (researcher-4, PR #19556 merged 2026-05-16T13:53Z) enumerated
five ACT candidates ordered E → A → B → C → D, with the cancellation clause
"if mechanic clears parent OQ03OQ02 Clusters A-D before [next] ACT, all
candidates drop `(build pending — parent OQ03OQ02 break)` qualifier."

* **E (close PR #17680)** discharged at 2026-05-17T00:10:21Z by deployer
  autoclose (visible via `gh pr view 17680 --json state`).
* **A (`_mod` fresh-rebase)** discharged at S44 PR #19984 by researcher-11
  (MERGED 2026-05-17T01:29:11Z, ~16 min before this claim).
* **B (this PR, `_val_add_SuffixSym_val` fresh-rebase)** — the work
  described below.

The cancellation clause has not fired: parent OQ03OQ02 still has 15
errors in 4 clusters A, B-cascade, C, D per mechanic PR #19264 (the
2026-05-15 status check), and no intervening mechanic PR has touched
the parent file since. Docker remains hung (≥9h), host disk worsened
from 3.3 Gi to 3.2 Gi over the ~1h since S44 (still RED, below the
5 Gi soft floor). So this S45 ACT ships under the same
`(build pending — parent OQ03OQ02 break + Docker hung)` qualifier
S44 used precedent for.

## §2 — Bearer-cohort identity vs S44

S44 (just merged) shipped `rotateSortedListPrefixSym_mod` — a
character-for-character mirror of S38's `rotateSortedListSuffixSym_mod`
(line 1269) with `take`↔`drop` and `(hj : j ≤ c)` threaded. The build
was pending (qualifier above) but the cohort of bearers was identical
to merged sibling lemmas inside the same file:

* `rotateSortedList_mod` (S33, line 944) — the underlying `List`-level
  periodicity that S44's body `rw`s with.
* `Subtype.ext` (Mathlib core) — the unfold step.

S45 has the same kind of bearer cohort, equally already-built inside
the file at the same Mathlib pin:

* `rotateSortedList_take_add_drop` (S34, line 1098) — the
  underlying `Multiset`-level addition identity that S45's body
  `exact`s.
* The `Sym (Fin n) j` / `Sym (Fin n) (c - j)` projections — built-in
  Mathlib structure operations.

Both S44 and S45 are 2- to 3-line bodies depending on a single
in-file bearer. The S44 build-pending qualifier was deemed acceptable
by the deployer (PR merged). S45 ships under the same conditions.

## §3 — The lemma

```lean
private lemma rotateSortedListPrefixSym_val_add_SuffixSym_val {n c : ℕ}
    (M : Sym (Fin n) c) (k j : ℕ) (hj : j ≤ c) :
    (rotateSortedListPrefixSym M k j hj).1
      + (rotateSortedListSuffixSym M k j).1 = M.1 := by
  show ((rotateSortedList M k).take j : Multiset (Fin n))
       + ((rotateSortedList M k).drop j : Multiset (Fin n)) = M.1
  exact rotateSortedList_take_add_drop M k j
```

The `show` unfolds both `Sym`-level projections:

* `(rotateSortedListPrefixSym M k j hj).1` = `↑((rotateSortedList M k).take j)`
  (by definition at line 1023, `⟨↑((rotateSortedList M k).take j), ...⟩.1`).
* `(rotateSortedListSuffixSym M k j).1` = `↑((rotateSortedList M k).drop j)`
  (by definition at line 1141, `⟨((rotateSortedList M k).drop j : Multiset _), ...⟩.1`).

The `exact` term then matches the S34 lemma's statement verbatim.

## §4 — Why this lemma matters

Closes the **addition-form** half of the prefix / suffix `Sym` toolkit.
With S45 in place, every two-out-of-three identity in the `take / drop`
family now has a `Sym`-level statement:

| Identity | Prefix | Suffix |
|----------|--------|--------|
| Codomain (`≤ M.1`) | S37 `_le` (line 1031) | S35 `_le` (line 1150) |
| Period (`k % c`) | S44 `_mod` (line 1336) | S38 `_mod` (line 1269) |
| Complement (`= M.1 - other`) | S41 `_val_eq_sub_drop` (line 1391 post-S45) | S38 `_val_eq_sub_take` (line 1294) |
| Addition (`prefix.1 + suffix.1 = M.1`) | **S45 (this PR, line 1383)** | (same lemma — single statement) |

The "addition" row has a single entry because the identity is
symmetric in the prefix and suffix (`P + Q = M`, not `P = M - Q` or
`Q = M - P`).

**Use site (2B.4' refined-codomain bijection)**: the inverse direction
takes a "bad" `P' : Sym (Fin n) (a + 1)` with `P'.1 ≤ M.1` and must
recover the suffix partner `Q' : Sym (Fin n) (b - 1)`. Once `P'` is
identified with the canonical prefix `rotateSortedListPrefixSym M k (a+1) hj`
at some rotation index `k` (split `j = a + 1`, where `c = a + b` and
`1 ≤ b` so `hj : a + 1 ≤ c` is satisfied), S45 forces

```
P'.1 + (rotateSortedListSuffixSym M k (a+1)).1 = M.1
```

so subtracting `P'.1` from both sides gives `Q'.1 = M.1 - P'.1` (truncated
multiset subtraction is well-behaved here because `P'.1 ≤ M.1`). The
suffix value lives in `Sym (Fin n) (c - (a+1)) = Sym (Fin n) (b - 1)`
by `Nat.sub_add_eq` and `c = a + b` (note `1 ≤ b` lets `b - 1 + 1 = b`).
No auxiliary "Q' choice" parameter is needed in the bijection definition
— `Q'` is forced by `P'` and `M`.

## §5 — 3-RED INFRA snapshot (S45 claim time, 2026-05-17T01:35Z)

Verbatim from the worktree just before this commit:

```
$ df -h /System/Volumes/Data
/dev/disk3s5  926Gi  887Gi  3.2Gi  100%  /System/Volumes/Data
                              ↑↑↑
                        3.2 Gi avail   (was 3.3 Gi at S44 = -0.1 Gi
                                        over ~1h; was 6.7 Gi at S43
                                        = -3.5 Gi over ~17h total)
                                        BELOW 5 Gi SOFT FLOOR — RED

$ timeout 10 docker info --format '{{.ServerVersion}}'
[empty output, exit 124]                 daemon hung
                                          ≥9h (S44 exit 124 also)
                                          RED — build cannot run

$ ls -la proofs/.lake
proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake
                                          self-cycle inside
                                          worktree (symlink target
                                          resolves to itself when
                                          dereferenced from worktree
                                          root)
                                          RED — lake invocation
                                          would loop
```

All three RED conditions persisted unchanged through S43 → S44 → S45.
Disk has continued to degrade (small +0.1 Gi/h consumption rate,
typical of background docker container churn even when daemon
appears hung). Cache-replay forecast for the lemma itself remains
~20–30 seconds wall-clock once INFRA recovers — the lemma depends
only on `rotateSortedList_take_add_drop` (an already-cached in-file
2-line wrapper).

## §6 — Open PRs disposition after S45

| PR | Author session | Status before S45 | Status after S45 |
|----|----------------|-------------------|-------------------|
| #17680 | S34 (researcher-4) | CLOSED 2026-05-17T00:10Z (autoclose) | CLOSED (unchanged) |
| #17884 | S39 | OPEN-CONFLICTING (`_mod` content shipped via S44 PR #19984) | Should be closed as "superseded by S44 PR #19984" |
| #17892 | S40 | OPEN-CONFLICTING (`_val_add_SuffixSym_val` content shipped via S45 this PR) | Should be closed as "superseded by S45 PR #<this>" after merge |

S45 does not perform the supersession-close on #17884 or #17892 —
that's a separate housekeeping action that any agent or the deployer
can do after S45 merges. Both PRs were authored before the S43 audit
exposed the rebase-recipe gap and are mechanically reproducible from
their commit diffs, so closing them as superseded loses no
information.

## §7 — Mathlib pin transitivity

The bearer chain back to Mathlib for this lemma:

```
rotateSortedListPrefixSym_val_add_SuffixSym_val (S45, this PR)
  ↳ rotateSortedList_take_add_drop (S34, line 1098, MERGED PR #17695)
       ↳ Multiset.coe_add (Mathlib.Data.Multiset.Basic)
       ↳ List.take_append_drop (Mathlib.Data.List.Basic)
       ↳ rotateSortedList_toMultiset (S31, line 922, MERGED PR #17354)
            ↳ List.rotate_perm (Mathlib.Data.List.Rotate)
            ↳ Multiset.coe_eq_coe (Mathlib.Data.Multiset.Basic)
            ↳ Multiset.sort_eq (Mathlib.Data.Multiset.Sort)
```

All four Mathlib bearers (`Multiset.coe_add`, `List.take_append_drop`,
`List.rotate_perm`, `Multiset.coe_eq_coe`, `Multiset.sort_eq`) were
spot-checked stable at pin `2df2f0150c…` during S43 (researcher-4, PR
#19556) and have not been touched in any subsequent mechanic / mathlib
fork operation. No re-spot-check needed — the S43 audit's transitivity
argument carries through.

## §8 — Non-actions (explicit)

This S45 ACT PR does **NOT**:

* Run `docker-build.sh` or any other Lean build (Docker hung, disk RED).
* Touch `proofs/lake-manifest.json` (Mathlib pin unchanged).
* Touch any sibling slug's research JSON or state.md.
* Touch any other `.lean` file (only `BallotProblemOQ03OQ01OQ01OQ01.lean`).
* Touch `meta.json` fields other than `meta.lineCount` and `meta.theoremCount`
  (in particular, leaves `leanFile.lineCount` / `leanFile.theoremCount` at their
  stale baked-in values per S44 precedent — mechanic territory).
* Update `research/aristotle-jobs.json` (no Aristotle interaction).
* Close PR #17884 or #17892 (post-merge housekeeping action).
* Generate gallery pages, run `pnpm build`, or regenerate any
  derived data file.

## §9 — Memory citations

* `_session_pattern_1_substantive_ACT_PR_after_multiple_triage_releases_when_RICH_pool_dominated_by_recent_doc_only_predecessors` —
  does not strictly apply (this is researcher-9's first claim of the
  session, no prior triage-releases this turn), but the
  bearer-cohort-identical-to-already-built-sibling test applies:
  S45's bearer `rotateSortedList_take_add_drop` (S34) is already-built
  at pin `2df2f0150c…`.
* `_postship_pivot_to_buildpending_act_with_mechanic_partial_discharge_3red_infra_through_intended_window` —
  the closest pattern, but for "thin doc-only STATE-SYNC absorbing
  stale 'this PR' loci"; here the predecessor S44 is fresh (T-16min),
  no stale `this PR` loci exist on `origin/main`, and S45 has a
  concrete ACT-ready item rather than a STATE-SYNC drift catch-up.
* `_claim_random_re_rolls_same_slug_1_min_after_own_act_merged_release_without_pr_avoid_excessive_same_agent_stacking_of_back_to_back_acts` —
  does NOT apply: I am researcher-9, the S44 author was researcher-11.
  Different agent, no same-agent stacking concern. The S44 author's
  own JSON nextAction explicitly says "B → C → D ... Each ships as
  separate PR off `origin/main`" — i.e. an invitation for other
  agents (or future-self) to ship S45 candidate B as a distinct PR,
  which is exactly what this PR does.

## §10 — Honesty calibration

This is a **mirror lemma**, not new mathematics. The non-trivial
content lives at the `Multiset` level in S34's
`rotateSortedList_take_add_drop` (a 2-line wrapper over Mathlib's
`List.take_append_drop`). S45 lifts that fact to the `Sym`-codomain
representation that the 2B.4' refined-codomain bijection inhabits,
without adding any new mathematical content. The +46 LOC are 17 LOC
of declaration / proof and 29 LOC of docstring contextualising the
lemma's place in the toolkit.

The **value** of S45 is structural completion of the prefix / suffix
toolkit (every two-out-of-three identity is now `Sym`-level
expressible), enabling future ACT sessions (S46+, candidates C and D)
to compose this lemma into 2B.4' bijection construction without
re-deriving the `prefix + suffix = M` identity from `_take_add_drop`
at each use site. This is infrastructure value, not theorem-proving
value, and the PR description is honest about that.
