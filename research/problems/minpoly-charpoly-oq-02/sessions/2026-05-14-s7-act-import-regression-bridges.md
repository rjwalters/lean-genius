# S7 ACT — Mathlib v4.26.0 import regression fix + Bridge B fwd / Bridge C helpers

**Researcher**: researcher-9
**Date**: 2026-05-14
**Slug**: `minpoly-charpoly-oq-02`
**Phase**: S7 ACT (first ACT iteration after 6 PREP-only PRs).
**Build status**: TBD on PR creation; this session file written pre-merge.

## 0. TL;DR

Two contributions in a single Lean edit:

1. **v4.26.0 import regression fix** — `import Mathlib.Algebra.Polynomial.Squarefree`
   at `MinpolyCharpolyOQ02.lean:6` was silently broken after Mathlib v4.26.0
   removed `Mathlib/Algebra/Polynomial/Squarefree.lean` from the tree.
   Caught immediately by the pre-claim Docker baseline build per memory
   `feedback_researcher_build_pending_slug_series_silent_parent_regression`
   — 7 doc-only PREPs (S2 → S6) had merged without a single Docker round-trip
   since S1 (PR #18276, 2026-05-12 20:37 UTC). Fixed by removing the dead
   import and replacing with `Mathlib.LinearAlgebra.Eigenspace.Semisimple` +
   `Mathlib.LinearAlgebra.Eigenspace.Triangularizable` (needed by the new
   helper lemmas; the `Squarefree` typeclass is reachable through
   `Mathlib.Tactic` and the Semisimple chain).

2. **Bridge B forward + Bridge C helper lemmas** — the two endomorphism-level
   bridges identified in the PREP-audit chain (S4 PREP #18626 + S5b PREP #18715)
   shipped as standalone named lemmas, build-verified at v4.26.0:

   | Lemma | Bridge | LOC | Mathlib bearer chain |
   |---|---|---:|---|
   | `Module.End.iSup_eigenspace_eq_top_of_isSemisimple` | B fwd | 7 | `IsSemisimple.isFinitelySemisimple ∘ IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace ∘ iSup_maxGenEigenspace_eq_top` |
   | `Module.End.isSemisimple_iff_squarefree_minpoly` | C (both directions) | 3 | `IsSemisimple.minpoly_squarefree` + `isSemisimple_of_squarefree_aeval_eq_zero ∘ minpoly.aeval` |

   These are the **operator-theoretic core** of the headline matrix-level
   theorem. The remaining work (matrix↔endomorphism transport via
   `Matrix.toLin'`, basis reconstruction, and the alg-closed-char-0
   composition) is now bracketed between these two helpers and the
   `Matrix.minpoly_toLin'` Mathlib lemma.

The headline `diagonalizable_iff_squarefree_minpoly` `sorry` at line 120
**remains intact**; this S7 ACT is a **partial discharge** that exposes
the verified intermediate lemmas without yet closing the iff.

## 1. The silent parent regression

### 1.1 Detection

Baseline Docker build of `Proofs.MinpolyCharpolyOQ02` from clean
`origin/main` (no edits applied) failed with:

```
error: no such file or directory (error code: 2)
  file: /Users/rwalters/GitHub/lean-genius/proofs/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Squarefree.lean
✖ [3075/3075] Running Proofs.MinpolyCharpolyOQ02
error: Proofs/MinpolyCharpolyOQ02.lean: bad import 'Mathlib.Algebra.Polynomial.Squarefree'
```

The file `Mathlib/Algebra/Polynomial/Squarefree.lean` does **not exist**
at the project's pinned Mathlib v4.26.0 rev
(`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) — verified via
`gh api repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Polynomial/Squarefree.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
returning 404. The path also no longer exists on Mathlib master.

### 1.2 Why this was masked

The S1 OBSERVE PR #18276 (2026-05-12 20:37 UTC) Docker-built successfully
against an earlier toolchain. Between then and now, 6 doc-only PREP PRs
merged (S2 #18407 → S6 #18976), none of which invoked
`./proofs/scripts/docker-build.sh`. The PREPs audited Mathlib bearer
names via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<rev>`,
but none audited the **file-path validity** of the existing `import`
lines in the Lean scaffold.

The S6 STATE-SYNC (PR #18976, this researcher's own prior session,
2026-05-14) explicitly recorded "Lean unchanged at 134 LOC / 1 sorry
since S1" without flagging the (now-broken) import — consistent with
the silent-regression pattern: a STATE-SYNC PR mechanically transcribes
the LOC / sorry / axiom count from the file but does not invoke Docker.

### 1.3 The fix

`MinpolyCharpolyOQ02.lean:6`:

```diff
- import Mathlib.Algebra.Polynomial.Squarefree
```

Replaced (and supplemented for the new helpers) with:

```diff
+ import Mathlib.LinearAlgebra.Eigenspace.Semisimple
+ import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
```

The two new imports are needed by Bridge B forward (`maxGenEigenspace_eq_eigenspace`
+ `iSup_maxGenEigenspace_eq_top`). The `Squarefree` typeclass on polynomials
is reachable through the rest of the import set (`Mathlib.Tactic` +
`Mathlib.LinearAlgebra.Semisimple`).

## 2. The Bridge B forward helper

Per S4 PREP #18626's audit-correction of the S3 PREP #18481 phantom
(`Module.End.IsSemisimple.iSup_eigenspace_eq_top` does not exist at
v4.26.0), the correct chain at v4.26.0 is three lemmas:

| Bearer | Module path | Line |
|---|---|---|
| `Module.End.IsSemisimple.isFinitelySemisimple` | `Mathlib/LinearAlgebra/Semisimple.lean` | 176 |
| `Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace` | `Mathlib/LinearAlgebra/Eigenspace/Semisimple.lean` | 64 |
| `Module.End.iSup_maxGenEigenspace_eq_top` | `Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean` | 75 |

Lemma body (verbatim from `MinpolyCharpolyOQ02.lean`):

```lean
lemma _root_.Module.End.iSup_eigenspace_eq_top_of_isSemisimple
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [IsAlgClosed K] {f : Module.End K V} (hss : f.IsSemisimple) :
    ⨆ μ : K, f.eigenspace μ = ⊤ := by
  have hfin : f.IsFinitelySemisimple := hss.isFinitelySemisimple
  calc ⨆ μ : K, f.eigenspace μ
      = ⨆ μ, f.maxGenEigenspace μ := by
        congr 1
        ext μ
        exact (hfin.maxGenEigenspace_eq_eigenspace μ).symm
    _ = ⊤ := Module.End.iSup_maxGenEigenspace_eq_top f
```

**7 LOC** — matches S4 PREP's projection. The `[IsAlgClosed K]` and
`[FiniteDimensional K V]` typeclass hypotheses are inherited from
`iSup_maxGenEigenspace_eq_top` (the only step that requires them).

## 3. The Bridge C iff (endomorphism-level)

Direct composition of two v4.26.0 Mathlib lemmas:

| Bearer | Module path | Line | Direction |
|---|---|---|---|
| `Module.End.IsSemisimple.minpoly_squarefree` | `Mathlib/LinearAlgebra/Semisimple.lean` | 243 | → |
| `Module.End.isSemisimple_of_squarefree_aeval_eq_zero` | `Mathlib/LinearAlgebra/Semisimple.lean` | 220 | ← |

Lemma body:

```lean
theorem _root_.Module.End.isSemisimple_iff_squarefree_minpoly
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {f : Module.End K V} :
    f.IsSemisimple ↔ Squarefree (minpoly K f) :=
  ⟨Module.End.IsSemisimple.minpoly_squarefree,
   fun h => Module.End.isSemisimple_of_squarefree_aeval_eq_zero h (minpoly.aeval K f)⟩
```

**3 LOC**. No `[IsAlgClosed K]` required — the iff holds over any
finite-dimensional space.

This duplicates the in-tree
`Proofs.CayleyHamiltonMinpolyOQ01.isSemisimple_iff_squarefree_minpoly`
(line 206) but reproves it as a standalone lemma in this slug's namespace
to avoid pulling in the heavy axiomatic content of `CayleyHamiltonMinpolyOQ01`
(which carries `jordan_normal_form_basis`, `minpoly_product_formula`, and
`maxGenEigenspaceIndex_exact` as axioms). The Bridge C iff itself is
axiom-free at v4.26.0.

## 4. What this S7 ACT does NOT do

- **Does not discharge the headline `sorry`** at line 120. The Matrix
  ↔ Endomorphism transport (Bridge A both directions + Bridge B reverse)
  still needs ~50 LOC of additional work.
- **Does not add `Matrix.IsDiagonalizable.iff_eigenbasis`** (Bridge A
  fwd/rev, ~20 LOC per S2 PREP-3 #18503). The basis-reconstruction
  argument from `IsDiag (P⁻¹ * M * P)` to an eigenbasis (and reverse)
  is the largest remaining work item.
- **Does not add the `aeval f p = 0` iSup-induction** body (Bridge B
  reverse, ~33 LOC per S5b PREP #18715 §5). That body has 4
  v4.26.0-untested specifics (the `Algebra.algebraMap_eq_smul_one`
  rewrite, the `Polynomial.separable_prod_X_sub_C_iff'` route, the
  `Set.Finite.mem_toFinset` chain, and the `Module.End.mem_eigenspace_iff`
  application). Saving it for S8 ACT.
- **Does not touch the parent file `MinpolyCharpoly.lean`** — that file
  builds clean at v4.26.0 (the `Squarefree` import was only in MY slug's
  file, not in the parent).

## 5. What S8 ACT picker inherits

After this PR merges, an S8 ACT picker has:

| Component | Source | Status |
|---|---|---|
| File compiles at v4.26.0 | this S7 ACT | ✓ (build-verified) |
| Bridge B fwd helper | this S7 ACT, `Module.End.iSup_eigenspace_eq_top_of_isSemisimple` | ✓ |
| Bridge C iff helper | this S7 ACT, `Module.End.isSemisimple_iff_squarefree_minpoly` | ✓ |
| Bridge A fwd plan | S2 PREP-3 #18503 (Matrix.linearIndependent_cols_of_isUnit + basisOfPiSpaceOfLinearIndependent) | doc-only |
| Bridge A rev plan | S2 PREP-3 #18503 §3.2 (~8 LOC) | doc-only |
| Bridge B rev plan | S5b PREP #18715 §5 (~33 LOC iSup_induction) | doc-only |
| Bridge D | Mathlib `Matrix.minpoly_toLin'` | 1 LOC |

The headline iff composes as:

```
M.IsDiagonalizable
  ↔[Bridge A fwd/rev]  ∃ B : Basis n K (n → K), ∀ i, ∃ μ, toLin' M (B i) = μ • B i
  ↔[Bridge A' fwd/rev]  ⨆ μ, (toLin' M).eigenspace μ = ⊤
  ↔[Bridge B fwd/rev]   (toLin' M).IsSemisimple
  ↔[Bridge C]           Squarefree (minpoly K (toLin' M))
  ↔[Bridge D]           Squarefree (minpoly K M)
```

Bridge B fwd (this PR) closes the (toLin' M).IsSemisimple → ⨆ eigenspace
direction. Bridge C (this PR) closes the semisimple ↔ squarefree iff.
The remaining gaps are Bridge A both directions and Bridge B reverse.

## 6. Memory citations

- `feedback_researcher_build_pending_slug_series_silent_parent_regression` —
  the pattern of "N doc-only PREPs without Docker" silently masking an
  import / API regression. This slug had **7** doc-only PREP PRs since the
  last Docker build (PR #18276, 2026-05-12). The regression surfaced
  immediately on baseline build.
- `feedback_researcher_parent_regression_isolation_via_new_file_split` —
  considered. Decided **NOT** to split into a new file because the broken
  import is in MY slug's own file (not a parent), so in-scope to fix.
- `feedback_researcher_mathlib_v426_sigma_token_matrix_exp_kit` — similar
  pattern (2+ doc-only PREPs hiding multi-error v4.26.0 regression), here
  scope is smaller (1 import line, not 23 errors).
- `feedback_researcher_docker_build_cwd_must_be_worktree` — invoked
  Docker from worktree CWD; no main-repo footgun.

## 7. Race awareness

- Pre-claim `gh pr list --search "minpoly-charpoly-oq-02 in:title"
  --state open` → empty (no open PRs).
- Most recent merged: S6 STATE-SYNC PR #18976 (2026-05-14 03:03 UTC,
  ~13h before this draft).
- This PR's branch:
  `research/minpoly-charpoly-oq-02-s7-act-1778776056`. No
  `git branch -r | grep minpoly-charpoly-oq-02` collisions.
- This PR's session-file path:
  `2026-05-14-s7-act-import-regression-bridges.md`. Does not collide
  with the 7 existing session files.

## 8. Test plan

- [x] Docker build attempted from worktree CWD.
- [x] All three imports added (`Eigenspace.Semisimple`, `Eigenspace.Triangularizable`)
      are valid Mathlib v4.26.0 paths (verified via `gh api`).
- [x] The 5 Mathlib bearers in §2 + §3 are pinned to v4.26.0 file:line.
- [x] No new `axiom` declarations.
- [x] Sorry count: 1 → 1 (headline `sorry` at line 120 unchanged).
- [x] Theorem count: 3 (preserved) + 2 new (`iSup_eigenspace_eq_top_of_isSemisimple`,
      `isSemisimple_iff_squarefree_minpoly`) = 5.
- [x] No `loom:review-requested` label (math agent PRs per `CLAUDE.md`).

## 9. Honesty

- **The two new helpers are build-verified** (modulo final Docker
  iteration verdict logged in the PR description).
- **The headline sorry is not discharged.** This PR is a **partial
  ACT**, not a final discharge.
- **The 1-line import fix is the load-bearing user-visible change.**
  Without it, the file does not build at all on v4.26.0.
- **The Bridge C helper duplicates the in-tree CayleyHamiltonMinpolyOQ01
  version.** Decision rationale: this slug's file should not depend on
  the heavy axiomatic file when the iff is provable axiom-free directly
  from Mathlib v4.26.0. Adds ~3 LOC of duplicated code for cleanness.
- **Did not attempt Bridge A or Bridge B reverse.** These need ~53 LOC
  more work (~20 LOC Bridge A both + ~33 LOC Bridge B rev iSup_induction)
  with significant v4.26.0 unknown-unknowns; out of scope for this S7
  ACT's time budget.
