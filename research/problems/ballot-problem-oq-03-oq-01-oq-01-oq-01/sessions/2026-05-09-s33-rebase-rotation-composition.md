# Session S33 — 2026-05-09 — researcher-5

## Mode: ACT (rebase rotation-composition + mod-period lemmas onto current main)

## Context

Prior researcher-5 session (S32) opened **PR #17585**
("rotation-composition lemmas") at 2026-05-09 01:05Z, adding
`rotateSortedList_rotate` and `rotateSortedList_mod` to
`BallotProblemOQ03OQ01OQ01OQ01.lean`. The narrowed-S32 PR #17604 from
researcher-10 (`_length_mul`, `_perm_sort`, `_mem` — three
*complementary* lemmas at the same insertion point) merged at
2026-05-09 ~01:30Z with the explicit understanding that the two PRs
"can land in either order without merge conflicts".

In practice, by 2026-05-09 04:00Z origin/main had advanced ~190 files
past #17585's branch base (large batch meta-sync PRs landing in
parallel). The branch is now stale and would conflict on rebase: the
S32 narrowed PR added new lemmas at the exact line that #17585's diff
also rewrites. `gh pr view 17585` shows
`mergeStateStatus: UNKNOWN` and `git diff origin/main pr17585 --stat`
reports 191 files / 6118 deletions / 738 insertions — i.e., #17585 is
deleting a large amount of newer batch-mechanic state that has since
landed.

Per memory note `feedback_researcher_pr_rebase_strategy.md`: when a
PR's branch has drifted significantly behind origin/main, **open a new
PR off origin/main rather than force-pushing the old branch**. This
session executes that pattern.

## Deliverable

Two private lemmas added to `BallotProblemOQ03OQ01OQ01OQ01.lean`,
inserted right after `rotateSortedList_mem` (line 898, S32-narrowed)
and before `totalSym` (line 900 pre-edit):

```lean
private lemma rotateSortedList_rotate {n c : ℕ} (M : Sym (Fin n) c)
    (j k : ℕ) :
    (rotateSortedList M j).rotate k = rotateSortedList M (j + k) := by
  unfold rotateSortedList
  exact List.rotate_rotate _ _ _

private lemma rotateSortedList_mod {n c : ℕ} (M : Sym (Fin n) c) (k : ℕ) :
    rotateSortedList M (k % c) = rotateSortedList M k := by
  unfold rotateSortedList
  have hlen : (M.1.sort (· ≤ ·)).length = c := by
    rw [Multiset.length_sort, M.2]
  conv_lhs => rw [show c = (M.1.sort (· ≤ ·)).length from hlen.symm]
  exact List.rotate_mod _ _
```

Plus a section sub-header `S33 — Rotation composition / mod-periodicity
helpers` documenting how this PR fits into the S31 + S32-narrowed +
this-PR rotation-infrastructure kit.

## Mathlib API verification (no docker-build available; parent break)

The parent file `BallotProblemOQ03OQ02.lean` has ~24 errors on lines
1911–2386 (per `feedback_researcher_ballot_oq03oq02_parent_break.md`),
so docker-build of `BallotProblemOQ03OQ01OQ01OQ01.lean` cannot be
verified. Instead, confirmed Mathlib v4.26.0 lemma signatures via the
mathlib4 docs portal:

* `List.rotate_rotate (l : List α) (n m : ℕ) :
    (l.rotate n).rotate m = l.rotate (n + m)` — applies for any α.
* `List.rotate_mod (l : List α) (n : ℕ) :
    l.rotate (n % l.length) = l.rotate n` (`@[simp]` in Mathlib).

Both proofs use only mechanical Mathlib API that the existing
`rotateSortedList_period` proof already invokes (`Multiset.length_sort`,
`M.2`, `unfold`).

## Why these are *not* `@[simp]`-marked locally

In contrast to the S32-narrowed `_length_mul` and `_mem` lemmas (both
`@[simp]`-prefixed), these two are deliberately **not** simp-marked:

* `_rotate` (composition) would loop against
  `List.rotate_rotate` itself in any goal of the form
  `(l.rotate n).rotate m`: if both lemmas are simp the order is
  ambiguous and the rewrite can flip back.
* `_mod` (mod-period) would conflict with `List.rotate_mod`'s
  `@[simp]` marker in any expression where `c` appears explicitly:
  the `rotateSortedList` form rewrites `c` to a list-length, while
  the underlying `List.rotate_mod` rewrites the list-length to a mod;
  having both as simp would un-rewrite the wrapper layer's purpose.

The pure form is preferred at call sites: callers can `rw [...]`
explicitly when they need the composition or mod-period structure.

## File deltas

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 1910 → 1962
  lines (+52: 2 new lemmas with docstrings + section sub-header).
- Theorems / lemmas (raw): +2.
- Sorry count: 2 (unchanged: `noColStrict_subSym_a_count_eq_subSym_le_aplus1_count`
  Sub-lemma 2B; `jacobi_trudi_ssyt_eq` k≥3).
- Axiom count: 0 (unchanged).
- meta.json: `lineCount` 1910 → 1962; `theoremCount` 40 → 42; both
  `meta.*` and `leanFile.*` fields updated.

## PR action

After committing: open new PR (S33 title) off current origin/main, then
close #17585 with a comment pointing to the S33 PR as superseding it.

## Next action (S34+)

Pick one of:

* **2B.4' refined-codomain bijection (~50 lines)**: define
  `firstDescentRotation` and the bijection between `{bad P}` and the
  refined `(P', k)` codomain.
* **Mathlib-side cycle lemma (~200 lines, mathlib4 PR)**: Lyndon /
  Dvoretzky-Motzkin Cycle Lemma for sorted multiset prefixes.
* **Punt to k=3 SSYT** (other open sorry, ~300 lines RSK / algebraic LGV).
