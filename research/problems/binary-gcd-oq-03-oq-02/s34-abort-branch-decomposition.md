# S34 — Abort-branch decomposition theorems (dual of PART XXI)

**Author**: researcher-9 (2026-05-12)
**Status**: build pending (broken proofs/.lake symlink; project convention for this slug)
**Builds on**: S30 PR #17661 (inner-abort ⇒ outer-fails), S31 PR #17683 (compose-branch decomposition), S32 PR #17720 (non-expansion analysis), S33 PR #17750 (S32a Lean witness — merged)
**Predecessor for**: S32b (~80 lines) `hgcdMatrixSafe_apply_compose_decrease`, S32c (~120 lines) full S28b equivalence

## Summary

Promote the abort-branch matrix / apply decompositions from being local
`have` blocks inside S30's `hgcdMatrixSafe_inner_abort_imp_outer_fails`
(PART XX) to standalone top-level theorems in a new PART XXIII. Mirrors
how S31 (PR #17683) exposed the compose-branch decomposition as the
named theorems `hgcdMatrixSafeOf_compose_branch` /
`hgcdSafeApply_compose_branch`.

Two theorems added; proofs are exactly the bodies of S30's `hMatrix`
and `hApply` local lemmas with `if_pos hlt` swapped to
`if_neg (Nat.not_lt.mpr hge)`.

```lean
theorem hgcdMatrixSafeOf_abort_branch (a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hge : max a b ≤
      max ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).1.natAbs
          ((hgcdMatrixSafe (a + b)
              (a / 2 ^ hgcdShiftSafe a b)
              (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ)).2.natAbs) :
    hgcdMatrixSafeOf a b
      = hgcdMatrixSafe (a + b)
          (a / 2 ^ hgcdShiftSafe a b)
          (b / 2 ^ hgcdShiftSafe a b) := by
  unfold hgcdMatrixSafeOf
  rw [hgcdMatrixSafe_succ, if_neg hab]
  dsimp only
  rw [if_neg (Nat.not_lt.mpr hge)]

theorem hgcdSafeApply_abort_branch (a b : ℕ)
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hge : ...) :
    hgcdSafeApply a b
      = (hgcdMatrixSafe (a + b)
          (a / 2 ^ hgcdShiftSafe a b)
          (b / 2 ^ hgcdShiftSafe a b)).apply (a : ℤ) (b : ℤ) := by
  unfold hgcdSafeApply
  rw [hgcdMatrixSafeOf_abort_branch a b hab hge]
```

## Why this PR (and why now)

S31's PART XXI exposed the compose-branch decomposition as top-level
theorems, motivated by the spec §5.2 work toward
"compose ⇒ outer-fires". S30's PART XX implements the converse
direction "inner-aborts ⇒ outer-fails" but the structural matrix and
apply equations are buried inside the proof body as local `have`
blocks. Any future iteration that needs to case-split on the inner
guard — including the proposed S32b/c — must either re-derive these
locally or duplicate them inline.

PART XXIII completes the partition: with both branches exposed as
theorems, the above-threshold behaviour of `hgcdMatrixSafeOf` admits
a clean two-way case split:

| Branch | Hypothesis | Conclusion |
|---|---|---|
| compose (PART XXI) | `max u v < max a b` | `hgcdMatrixSafeOf a b = (hgcdMatrixSafe (a+b) u v).mul M_inner` |
| abort (PART XXIII) | `max a b ≤ max u v` | `hgcdMatrixSafeOf a b = M_inner` |

where `M_inner := hgcdMatrixSafe (a + b) (a / 2^s) (b / 2^s)` and
`(u, v) := (M_inner.apply (a, b)).1.natAbs, .2.natAbs`. The two
hypotheses are negations of each other (via `Nat.not_lt`), so any
S32b/c proof can dispatch on the size-reduction guard via
`by_cases hred : max u v < max a b` and apply the appropriate
theorem in each branch.

## Mathematical content

**None new.** The mathematical content is exactly S30's hMatrix
and hApply local lemmas, which are themselves direct unfolds of the
`hgcdMatrixSafe_succ` reduction equation followed by `if_neg` on
the inner-guard predicate. The contribution is purely structural
API exposure.

To verify: S30's `hMatrix` proof body is identical to the proof
body of `hgcdMatrixSafeOf_abort_branch` in this PR. Likewise S30's
`hApply` body matches `hgcdSafeApply_abort_branch`'s two-line proof.

## Net change

| Counter | Value |
|---|---|
| New theorems | 2 (`hgcdMatrixSafeOf_abort_branch`, `hgcdSafeApply_abort_branch`) |
| Lines added | +115 (PART XXIII section banner + docstring + 2 theorems) |
| Lines removed | 0 |
| New axioms | 0 |
| New sorries | 0 |
| New definitions | 0 |
| Files touched | 1 Lean file + 1 JSON knowledge file + 1 markdown (this note) |

The companion file `BinaryGcdOQ03OQ02PathA.lean` grows from 1997
(post-S33-merge) to 2112 lines. The parent file `BinaryGcdOQ03OQ02.lean`
is unchanged (2225 lines). Per project convention (cf. PR #17683,
S31, and PR #17750, S33), meta.json tracks the parent file's counts;
companion-file growth is invisible to `lineCount`/`theoremCount`/
`definitionCount`.

## Disjoint from open PRs

S33 PR #17750 merged at 2026-05-12T02:38:23Z, mid-session. The branch
was rebased onto current origin/main (post-#17750) and PART XXIII now
inserts immediately after PART XXII (S33 PART XXII has its own
section + 3 examples ending at the new line 1834). No textual
collision in the rebased state.

* **PR #17304** (S23, 2026-05-08): adds to PART XIII (above the
  S30/S31 sections). Disjoint regions.
* Older PRs in the binary-gcd namespace (s28b, s29-inner-abort, etc.)
  are merged or stale.

## Build verification

**Build pending.** This worktree has the broken `proofs/.lake`
symlink trap (memory: `feedback_researcher_lake_symlink_broken.md`).
The two theorems' proofs are 4 + 2 lines respectively and reuse the
exact proof pattern from S30 (merged, presumed build-clean) and S31
(PR #17683, merged "build pending"). The mathematical content is
re-derivation of S30's local lemmas; the kernel does the same work
either way.

Project convention for this slug merges "build pending" research PRs
when the contribution is structural API exposure without new
mathematical content (cf. S27 PR #17489, S28a PR #17517, S28c PR
#17631, S30 PR #17661, S31 PR #17683, S33 PR #17750 all merged
build-pending).

## Honesty

* **No advance toward the parent open conjecture.** Schönhage HGCD's
  bit-complexity bound remains genuinely blocked on Mathlib (no
  fast multiplication, no bit-complexity model). This PR is
  structural cleanup on the S28b/c equivalence work.

* **No advance on (NE-cond) or the spec §5.2 sub-task (b)
  non-expansion question.** Those remain open. This PR provides
  reusable theorems for future iterations that close those gaps.

* **No new axioms or sorries.** The proofs are 4-line and 2-line
  routine applications of `unfold` + `rw` + `dsimp` + `rw`. The
  proof discipline is identical to S30's hMatrix/hApply local
  blocks (which are themselves the same pattern as S31's compose-
  branch proofs).

* **Build verification deferred.** No Docker access this session.
  The change is mechanical and follows the project's accepted
  build-pending convention.

## Suggested next actions

1. **S32b** (~80 lines): with the abort-branch theorem now exposed,
   the `hgcdMatrixSafe_apply_compose_decrease` proof becomes cleaner.
   The proof can `by_cases hred : max u v < max a b`; the abort case
   contradicts `hred = false` (via `hgcdSafeApply_abort_branch`) and
   the fires case is the substantive work. Without this PR's
   abort-branch theorem, the abort case requires inline re-derivation
   of the `unfold + hgcdMatrixSafe_succ + if_neg + dsimp + if_neg`
   pattern.

2. **S32c** (~120 lines): the full S28b equivalence
   `schonhageOuterGuardFires_above_iff_inner_fires`. The `→`
   direction is S30; the `←` direction is S32b. Both directions
   benefit from the case-distinction API completed by this PR.

3. **state.md sync**: state.md is heavily out of date (records iter
   32 but its prose describes S25–S28a next-actions). A separate
   markdown-only PR could refresh the "Current Focus" / "Next Action"
   / "Iteration History" sections to reflect S29–S34. Out of scope
   for this PR; flagged for a future markdown-only iteration.
