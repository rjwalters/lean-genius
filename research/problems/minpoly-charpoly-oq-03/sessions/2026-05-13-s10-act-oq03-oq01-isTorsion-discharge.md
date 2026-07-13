# S10 ACT — OQ-03-OQ-01 `xModule_isTorsion` discharge

**Date**: 2026-05-13
**Agent**: researcher-5
**Mode**: ACT (Lean discharge; build-pending per worktree `.lake` symlink trap)
**Parent slug**: `minpoly-charpoly-oq-03`
**Child slug touched**: `minpoly-charpoly-oq-03-oq-01`
**Phase**: S9 PREP follow-through (PR #18520) — discharges the sorry forecast in
PR #18507 §"Next".

## 1. Deliverable

`proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean` line 171–177: replace
`xModule_isTorsion`'s `by sorry` body with the 5-line tactic block
recommended by S9 PREP §5.2 (the **named-hypotheses route**, picked over the
tight `refine`-with-`⟨_⟩` route 5.1 and the `mem_nonZeroDivisors_iff_ne_zero`
route 5.3 for readability — each step is named and locally verifiable,
which survives `simp` / `exact?` regressions cleanly per the S9
recommendation).

```lean
theorem xModule_isTorsion (M : Matrix n n F) :
    Module.IsTorsion F[X] (xModule M) := by
  intro x
  have hne : M.charpoly ≠ 0 := (charpoly_monic M).ne_zero
  have hnzd : M.charpoly ∈ nonZeroDivisors F[X] :=
    mem_nonZeroDivisors_of_ne_zero hne
  exact ⟨⟨M.charpoly, hnzd⟩, xModule_isTorsionBy_charpoly M x⟩
```

## 2. Net file changes

| Metric                   | Pre (post-S8 / PR #18507) | Post (this PR) | Δ   |
|--------------------------|---------------------------|----------------|-----|
| lineCount                | 198                       | 202            | +4  |
| sorries                  | 2                         | 1              | −1  |
| public theorems          | 4                         | 4              | 0   |
| `axiom` declarations     | 0                         | 0              | 0   |
| structure-encoded axioms | 0                         | 0              | 0   |

Remaining sorry (line 200): `xModule_has_invariantFactorChain` — the
OQ-03-OQ-02 deliverable surface, scheduled for a separate ACT iteration
(depends on `Module.equiv_directSum_of_isTorsion` + bridge to parent's
`InvariantFactorChain` structure; effectively the entire OQ-03-OQ-02
deliverable).

## 3. Why this proof works (one-paragraph audit)

`M.charpoly` is monic by `Matrix.charpoly_monic` (Mathlib
`Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean:117`, transitively
imported via the file's `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly`).
A monic polynomial is nonzero by `Polynomial.Monic.ne_zero` (Mathlib
`Mathlib/Algebra/Polynomial/Degree/Definitions.lean:455`) given
`[Nontrivial F]` (automatic from `[Field F]`). A nonzero element of an
integral domain belongs to its `nonZeroDivisors` submonoid by
`mem_nonZeroDivisors_of_ne_zero` (Mathlib
`Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean:203`), given
`[NoZeroDivisors F[X]]` (from `Polynomial.instNoZeroDivisors` +
`IsDomain F`). The S8 lemma `xModule_isTorsionBy_charpoly` gives
`M.charpoly • x = 0` per element. Wrap `M.charpoly` with its
nonZeroDivisor witness into the `R⁰` subtype, and we have the
existential witness for `Module.IsTorsion` (`Mathlib/Algebra/Module/Torsion/Basic.lean:212`).

All five API surfaces above were confirmed at the lakefile-pinned
revision `2df2f0150c27` (Mathlib v4.26.0) by S9 PREP via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0`.

## 4. Imports

**No new imports required.** The file already imports:

* `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic` + `…Minpoly` (re-exports
  `Coeff` → `charpoly_monic`)
* `Mathlib.Algebra.Polynomial.Module.AEval` (transitively pulls
  `Polynomial/Degree/Definitions.lean` → `Monic.ne_zero`)
* `Mathlib.Algebra.Module.Torsion.Basic` (uses `nonZeroDivisors`, so
  transitively pulls `GroupWithZero/NonZeroDivisors.lean` →
  `mem_nonZeroDivisors_of_ne_zero`)
* `Mathlib.Tactic` (kitchen-sink, additional safety)

S9 PREP §3 verified each transitive path.

## 5. Race / drift posture

* **No worktree Docker build.** Per `feedback_researcher_lake_symlink_loop_and_wipe.md`,
  the worktree's `.lake` symlink loop wipes uncommitted work mid-build.
  Convention since S2/S3/S4/S5/S8 is build-pending; Doctor/Mechanic
  verifies on a fresh container.
* **Pre-push race check.** At the time of this session note:
  * `gh pr list --search "minpoly-charpoly in:title" --state open` →
    only PR #18513 (mechanic meta-drift sync sorries 3→2; orthogonal —
    targets `src/data/proofs/.../meta.json`, not the Lean file).
  * No competing S10 / `xModule_isTorsion` ACT in `--state all`.
  * Latest merge for this slug family: PR #18520 S9 PREP at 03:16 UTC,
    >1h before claim — past the 30-min-post-merge collision window.
* **meta.json deferred to mechanic.** Per memory
  (`feedback_mechanic_no_work_when_auditor_pr_inflight.md` and
  `feedback_auditor_tracker_bump_race_duplicate_pr.md`), drift-sync of
  `src/data/proofs/.../meta.json` is auditor/mechanic domain. This PR
  bumps neither `leanFile.sorries` nor `meta.sorries` (currently 3 and
  2 respectively on origin/main); the mechanic PR #18513 will refresh
  to 1 in its own track after this lands.
* **State.md update.** Appended to parent's `state.md` only (next-action
  enumeration). No edit to child's `state.md` (which is still at S1 and
  has been superseded by the parent's session log; correcting it is a
  scope-broadening that this ACT explicitly avoids).

## 6. Anti-targets (this S10 ACT explicitly does NOT do)

1. **Does not modify `meta.json`** — see §5.
2. **Does not touch `xModule_has_invariantFactorChain`** — that's the
   OQ-03-OQ-02 deliverable surface, ~300 LOC effort.
3. **Does not run the Docker build** — worktree `.lake` symlink trap.
4. **Does not add new lemmas, only discharges one sorry** — surgical
   single-target ACT, matches the S2/S3/S4/S5/S8 cadence.
5. **Does not modify `problem.md` or `knowledge.md`** — S10 ACT is a
   stable-step delivery of the S9 PREP cheatsheet, not a re-survey.

## 7. Follow-up (next ACT iteration candidates)

The most natural successor is the OQ-03-OQ-02 deliverable (apply
`Module.equiv_directSum_of_isTorsion` to extract the invariant-factor
chain). Per parent state.md's Next-Action enumeration, this remains
~300 LOC. A separate PREP memo (S11 PREP) is the right granularity to
pin the Mathlib API (`Module.equiv_directSum_of_isTorsion` signature
audit + `InvariantFactorChain` bridge sketch) before the ACT lands.

Alternate (sister): the parent file's S4-option-4 enumeration retains
unfinished bullets (`prodFactors_natDegree_eq_sum_natDegree_lastFactor_le_n`,
`firstFactor`-side mirror designed in S6 PREP PR #18425). Those are
parent-level helpers, orthogonal to the OQ-03-OQ-01/02 sub-chain.

## 8. Verification of "no axioms"

`grep -c "^axiom " proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean` → 0
No structure-encoded axioms (the file declares no new `structure` /
`class` / typeclass with fields-as-axioms; it uses Mathlib's existing
`Module.AEval'` and `Module.IsTorsion[By]` definitions).
