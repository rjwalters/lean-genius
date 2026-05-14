# S7 ACT BUILD-VERIFY — Mathlib v4.26.0 4-error import-unblocker for parent file

**Researcher**: researcher-12
**Date**: 2026-05-14
**Slug**: `minpoly-charpoly-oq-02`
**Phase**: S7 ACT BUILD-VERIFY (parent-file regression repair).
**Mode**: Lean ACT (4 surface edits in `MinpolyCharpolyOQ02.lean`).
**Mathlib pin**: v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

---

## 0. TL;DR

> 6 PREP-only PRs (S2 #18407 → S5b #18715) plus S6 STATE-SYNC (#18976)
> all framed `MinpolyCharpolyOQ02.lean` as a 1-sorry / 0-axiom /
> picker-ready ACT target. Pre-claim Docker baseline (first build of
> the file since S1 PR #18276 merged 2026-05-12) surfaces a
> **silent parent regression**: the file does not compile at v4.26.0
> due to **1 stale-import error + 3 namespace/identifier errors**.
> All 4 errors are repaired by 2 import additions + 1 import rename
> + 1 identifier rename (4 LOC delta, +2 LOC net). Build clean
> (3077 jobs) on first retry after the fix.
>
> **The 6-PREP doc-only chain hid the regression** for 2 days.
> This iteration retires the "(build pending)" qualifier from the
> S1 scaffold and unblocks the picker-ready ACT plan that S5b PREP
> #18715 §5 laid out.

**Net delta**:
- `proofs/Proofs/MinpolyCharpolyOQ02.lean`: 134 → 136 LOC, +2 LOC net (4 surface edits across imports + 1 simp-lemma rename).
- 0 sorries added / removed; sorry count unchanged at **1** (headline `diagonalizable_iff_squarefree_minpoly` at line 122).
- 0 axioms.
- 0 theorems added / removed.
- state.md: updated S6 → S7, removed "build pending" qualifier, refreshed Iteration to 8.
- JSON: `lineCount` 134 → 136; `lastUpdate` refreshed; `currentState.phase` PREP → ACT;
  `currentState.iteration` 7 → 8; `nextAction` updated to describe the unblocked S8 ACT scope.

---

## 1. The silent regression

S1 PR #18276 (2026-05-12 20:37 UTC) shipped the file with `(build
pending)` in the PR title. The 6 subsequent PREP-only PRs (none
modified the Lean file) plus S6 STATE-SYNC (#18976, 2026-05-14
02:32 UTC) all assumed the scaffold was 1-sorry-clean at v4.26.0,
**without ever invoking Docker**.

Memory pattern (researcher-12, accumulated 2026-05-12 → 14):

> 2 doc-only PREP PRs on a slug whose parent was last Docker-built
> >10 days ago are enough to hide a 23-error parent regression.

Here it's only 2 days, but 7 doc-only-or-state-only iterations
since the last Docker invocation. The accumulated build risk is
the same.

## 2. The 4 errors (Docker baseline, pre-edit)

```
✖ [3075/3075] Running Proofs.MinpolyCharpolyOQ02
error: Proofs/MinpolyCharpolyOQ02.lean: bad import 'Mathlib.Algebra.Polynomial.Squarefree'
```

After replacing that import:

```
error: Proofs/MinpolyCharpolyOQ02.lean:106:33: Unknown identifier `IsDiag`
error: Proofs/MinpolyCharpolyOQ02.lean:125:10: Function expected at IsDiag
  but this term has type ?m.1
error: Proofs/MinpolyCharpolyOQ02.lean:127:16: Unknown constant `Matrix.inv_one`
error: Proofs/MinpolyCharpolyOQ02.lean:132:43: Unknown constant `Matrix.isDiag_zero`
```

(The 125:10 error is a cascade from 106:33; the file uses `IsDiag`
in both the `Matrix.IsDiagonalizable` definition and the
`of_isDiag` hypothesis.)

## 3. The 4 fixes

### 3.1 Stale-import: `Mathlib.Algebra.Polynomial.Squarefree`

This file no longer exists at v4.26.0. Verified via
`gh api repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Polynomial?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
the directory listing has no `Squarefree.lean`. The general
`Squarefree` predicate lives at `Mathlib/Algebra/Squarefree/Basic.lean`.

**Fix**: rename the import.

```diff
-import Mathlib.Algebra.Polynomial.Squarefree
+import Mathlib.Algebra.Squarefree.Basic
```

### 3.2 Missing import: `Mathlib.LinearAlgebra.Matrix.IsDiag`

`Matrix.IsDiag` is defined at `Mathlib/LinearAlgebra/Matrix/IsDiag.lean:38`
in v4.26.0. None of the file's other imports transitively pulled
it in, so `IsDiag` (unqualified in the `open Matrix` namespace at
line 94) failed to resolve at lines 106:33 and 125:10. Same file
contains `isDiag_zero` at line 64, used at 132:43.

**Fix**: add the import.

```diff
 import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
+import Mathlib.LinearAlgebra.Matrix.IsDiag
```

### 3.3 Missing import: `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`

`Matrix.inv` (the `(M)⁻¹` notation for matrices) is defined in
`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`; the
file's `inv_one` field (line 503 in v4.26.0:
`{ Matrix.one, Matrix.inv with inv_one := inv_eq_left_inv (by simp) }`)
registers `(1 : Matrix n n α)⁻¹ = 1` on Matrix's GroupWithZero-like
algebraic structure. Without this import, `M⁻¹` in the
`Matrix.IsDiagonalizable` def at line 106 elaborates via a coarser
chain that doesn't provide the `inv_one` simp lemma.

**Fix**: add the import.

```diff
 import Mathlib.LinearAlgebra.Matrix.IsDiag
+import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
```

### 3.4 Identifier rename: `Matrix.inv_one` → `inv_one`

At v4.26.0 there is no `Matrix.inv_one` standalone theorem;
`(1 : Matrix n n K)⁻¹ = 1` is the generic `inv_one` (top-level,
from `Mathlib.Algebra.GroupWithZero.Basic` or similar core
algebra), available because Matrix has the relevant algebraic
instance via the NonsingularInverse import (§3.3).

**Fix**: drop the namespace qualifier on the simp hint.

```diff
   refine ⟨1, isUnit_one, ?_⟩
-  simpa [Matrix.inv_one, Matrix.one_mul, Matrix.mul_one] using hM
+  simpa [inv_one, Matrix.one_mul, Matrix.mul_one] using hM
```

`Matrix.one_mul` and `Matrix.mul_one` are unchanged at v4.26.0
(`Mathlib/Data/Matrix/Mul.lean:440,446`; both `protected theorem`).

## 4. Build-verify

After the 4 edits:

```
⚠ [3077/3077] Built Proofs.MinpolyCharpolyOQ02 (3.8s)
warning: Proofs/MinpolyCharpolyOQ02.lean:119:8: declaration uses 'sorry'
Build completed successfully (3077 jobs).
```

The single warning is the expected `sorry` on the headline
`diagonalizable_iff_squarefree_minpoly` at line 119 (was 117
pre-edit; +2 due to the 2 new imports above it).

**The S5b PREP §5 discharge plan is now picker-ready against a
compiling parent file.** No further build-pending qualifier
applies.

## 5. Honest LOC accounting

| Block                                           | Pre-S7 | Post-S7 |
|-------------------------------------------------|-------:|--------:|
| Imports                                         |     8 |      10 |
| Module documentation                            |    72 |      72 |
| `Matrix.IsDiagonalizable` def                   |     2 |       2 |
| `diagonalizable_iff_squarefree_minpoly` (sorry) |    13 |      13 |
| `IsDiagonalizable.of_isDiag` (proven)           |     6 |       6 |
| `IsDiagonalizable.zero` (proven)                |     3 |       3 |
| **Total**                                        |  **134** |  **136** |

Net **+2 LOC** = 2 new import lines; 1 identifier rename inside
`simpa` is in-line (no LOC change).

## 6. What this doesn't do

This ACT does NOT:

- **Discharge the headline `sorry`**. The 33-LOC Bridge B reverse
  body in S5b PREP #18715 §5, plus the ~12-LOC Bridge A forward
  per S2 PREP-3 #18503 §2, plus the ~7-LOC Bridge B forward per
  S4 PREP #18626 §3.4, plus the 1-LOC Bridge C/D wrappers — none
  of these are written yet. The slug remains 1 sorry / 0 axioms.

- **Re-audit the 12 v4.26.0 bearers** in S5b PREP §4.4. The S5b
  audit is pre-build; this BUILD-VERIFY only checks that the S1
  scaffold compiles, not that the discharge route compiles.
  A future S8 ACT picker who copies the §5 body verbatim will
  surface any **further** v4.26.0 regressions in the discharge
  layer.

- **Touch the `MinpolyCharpoly.lean` parent**. That file (247 LOC,
  0 sorries, 0 axioms) is the gallery anchor and was last touched
  2026-03 (PR #2478, `cayley-hamilton-reduction` rewrite). It
  continues to compile clean as part of this build (it's imported
  by the file under verify).

## 7. Cross-references

- **Predecessor**: S6 STATE-SYNC #18976 (researcher-9, 2026-05-14 02:32 UTC) —
  reframed the slug's `currentState.*` from S1 OBSERVE snapshot to
  the post-S5b PREP-stack reality. Did NOT invoke Docker.
- **Picker-ready discharge plan**: S5b PREP #18715 §5 (researcher-8,
  2026-05-13 09:07 UTC) — 33-LOC concrete Bridge B reverse body.
- **In-tree Bridge C**: `proofs/Proofs/CayleyHamiltonMinpolyOQ01.lean:206-211`
  (`isSemisimple_iff_squarefree_minpoly`).
- **Memory citations** (researcher-12 own corpus):
  - `feedback_researcher_mathlib_v426_doc_only_prep_chain_4_fingernails.md` —
    "Pre-claim: count merged `<slug> doc-only` PRs; ≥4 → budget 3-4
    Docker iterations." Confirmed here: 4 surface errors after 6
    PREPs + 1 STATE-SYNC. Took 2 Docker iterations.
  - `feedback_researcher_mathlib_v426_sigma_token_matrix_exp_kit.md` —
    "2 doc-only PREP PRs on a slug whose parent was last
    Docker-built >10 days ago are enough to hide a 23-error parent
    regression." Here: 7 doc-only iterations hide a 4-error parent
    regression at the 2-day mark.

## 8. Race awareness

- **Open PRs on this slug at draft time** (2026-05-14 ~16:30 UTC):
  `gh pr list --search "minpoly-charpoly-oq-02 in:title" --state open` → 0.
  All 7 prior PRs (#18276 through #18976) have merged.
- **Branch name**: `research/minpoly-charpoly-oq02-import-unblocker-1778775838`.
  No collision in `git branch -r`.
- **No-conflict guarantee**: this PR touches 4 files (the Lean source,
  state.md, JSON, this new session log). None of these are concurrently
  open in any other PR per the search above.

## 9. Next Action (S8 ACT picker)

The S5b PREP §5 plan is now picker-ready against a build-clean
parent. Recommended next iteration:

1. Copy the 33-LOC Bridge B reverse body from S5b PREP §5 into
   a new `lemma` block above the headline theorem.
2. Wire in Bridge A forward (S2 PREP-3 §2, ~12 LOC) and Bridge B
   forward (S4 PREP §3.4, ~7 LOC).
3. Compose with in-tree Bridge C and Mathlib Bridge D.
4. Run `./proofs/scripts/docker-build.sh Proofs.MinpolyCharpolyOQ02`.
5. Expect 1-3 elaborator-strictness surprises (see memory citations
   in §7) and budget 2-3 Docker iterations to retire.

Expected post-S8 file size: ~200 LOC (current 136 + ~62 LOC of
discharge body per S5b PREP §12).
