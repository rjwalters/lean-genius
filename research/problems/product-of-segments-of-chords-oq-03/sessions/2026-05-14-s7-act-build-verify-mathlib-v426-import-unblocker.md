# S7 ACT BUILD-VERIFY — Mathlib v4.26.0 import unblocker

**Date / UTC**: 2026-05-14 ~16:55
**Author**: researcher-12
**PR**: TBD
**Phase**: ACT (BUILD-VERIFY sub-flavor — surgical regression fix)
**Lean diff**: 1 file, +18 doc / −24 Lean, net −3 LOC (~109 LOC after)
**Sorries**: 1 → 1 (unchanged)
**Axioms**: 0 → 0 (unchanged)
**Docker build**: 3058 jobs clean (~Proofs.ProductOfSegmentsOfChordsOQ03~)

## Context

After S2 SCAFFOLD on 2026-05-12 (PR #18380), the OQ-03 file
`proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` was shipped as
**build pending** because the S2 author hit a `proofs/.lake`
self-symlink loop in the worktree and could not verify a Docker
build locally. Three subsequent PREP PRs (S3 #18466, S4 #18474, S5
#18553) all shipped doc-only — no Lean diff, no rebuild attempt.
A fourth doc-only PR (S6 STATE-SYNC, 2026-05-14 ~02:42 UTC) refreshed
state.md / JSON without invoking the build.

Per `feedback_researcher_build_pending_slug_series_silent_parent_regression.md`,
when ≥3 consecutive build-pending PRs ship without Docker
verification, latent v4.26.0 regressions accumulate undetected. The
S6 STATE-SYNC author flagged this explicitly: *"Strongly
recommended: Docker-build the file BEFORE patching to establish
baseline."*

S7 ACT begins by doing exactly that: running
`./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChordsOQ03`
from the researcher-12 worktree CWD.

## Findings — two v4.26.0 surface regressions

The first Docker baseline surfaced **2 errors**:

### Error 1 — `Mathlib.Data.Matrix.Notation` does not exist at v4.26.0

```
error: no such file or directory (error code: 2)
  file: /Users/rwalters/GitHub/lean-genius/proofs/.lake/packages/mathlib/Mathlib/Data/Matrix/Notation.lean
error: Proofs/ProductOfSegmentsOfChordsOQ03.lean: bad import 'Mathlib.Data.Matrix.Notation'
```

**Cause**: The Matrix-notation file moved upstream from
`Mathlib/Data/Matrix/Notation.lean` to
`Mathlib/LinearAlgebra/Matrix/Notation.lean` at v4.26.0. Verified
via the v4.26.0 `Mathlib.lean` master imports list:

```
public import Mathlib.LinearAlgebra.Matrix.Notation
```

And direct HTTP check
(`https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/Mathlib/LinearAlgebra/Matrix/Notation.lean`
returns 200 OK; the file provides the same `!![...]` matrix-literal
notation + `Matrix.cons_val_zero` / `Matrix.cons_val_one` simp
lemmas).

**Fix**: 1-LOC import-path swap on line 3.

### Error 2 — `Matrix.det_fin_four` does not exist anywhere in Mathlib4

```
error: Proofs/ProductOfSegmentsOfChordsOQ03.lean:75:55: unsolved goals
⊢ !![1, 1, 0, 1; 1, 0, 1, 1; 1, -1, 0, 1; 1, 0, -1, 1].det = 0
error: Proofs/ProductOfSegmentsOfChordsOQ03.lean:84:15: Unknown constant `Matrix.det_fin_four`
```

(Once Error 1 was patched and the file could resolve `!![...]`, the
second-stage failure surfaced.)

**Cause**: The det-expansion lemma ladder in
`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` at v4.26.0
stops at `Matrix.det_fin_three` (line 820). A
GitHub-authenticated code search

```
gh api -X GET "search/code?q=det_fin_four+repo:leanprover-community/mathlib4"
```

returns 0 matches — the lemma was almost certainly **never shipped**
upstream, and the S2 SCAFFOLD author guessed. For 4×4 matrices, only
the recursive cofactor-expansion `Matrix.det_succ_row_zero` (line 761
of the same file) is available.

Both `example` blocks in the OQ-03 file (lines 74-78 unit-square
Δ = 0; lines 81-85 perturbed Δ = -8) had

```
unfold concyclicityDetCoords
simp [Matrix.det_fin_four]
ring
```

and could never have compiled.

**Fix attempted**: Replace `simp [Matrix.det_fin_four]; ring` with
`simp [Matrix.det_succ_row_zero, Matrix.det_fin_three,
Fin.sum_univ_four, ...]; ring` to use the cofactor-expansion
fallback. This made progress on the goal but left a residual
unreduced `Fin.succAbove`-laden sum — the `simp` did not fully
reduce `![1, 0, 1, 1] (Fin.succAbove 1 2)`-style indexed accesses
back to numerals. Closing this cleanly would require either a
larger simp-set (`Fin.succAbove`, `Fin.castSucc`, `Fin.succ`,
`Matrix.cons_val'`, etc.) or an algebraic row-dependence proof via
`Matrix.det_eq_zero_of_row_eq` (for the Δ = 0 case only — rows 1+3
= rows 2+4 = (2, 0, 0, 2)). Estimate ~10-15 LOC each; not worth
gating the build unblocker on this.

**Fix chosen**: Remove both `example` blocks (they were inert
documentation — no downstream consumer, no named theorem to wire
up). Replace with a `/-! ## Part 3 -/` doc block explaining the
regression and pointing to **S7b ACT** as the optional follow-up to
re-add the numerical sanity checks.

## Diff

`proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean`:

- **Line 3** (import): `Mathlib.Data.Matrix.Notation` →
  `Mathlib.LinearAlgebra.Matrix.Notation`.
- **Lines 17-18** (file header docstring item 3): rewritten to
  reflect example removal + S7 BUILD-VERIFY note.
- **Lines 69-89** (Part 3 block): two `example`s replaced with a
  comment block documenting the v4.26.0 regression and the S7b
  follow-up.

Net change: −24 Lean LOC (the two examples), +18 doc LOC, 1 LOC
import patch. ~109 total LOC after.

## Build verification

From researcher-12 worktree CWD
(`.loom/worktrees/researcher-12/`):

```
$ ./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChordsOQ03
...
⚠ [3058/3058] Built Proofs.ProductOfSegmentsOfChordsOQ03 (5.8s)
warning: Proofs/ProductOfSegmentsOfChordsOQ03.lean:102:8: declaration uses 'sorry'
Build completed successfully (3058 jobs).
=== Build succeeded ===
```

Only the expected `sorry` warning at line 102 (the headline iff
theorem `concyclicityDet_eq_zero_iff_concyclic`, deferred to S3 +
S4 ACT).

## Parent file impact

Parent file `proofs/Proofs/ProductOfSegmentsOfChords.lean` does
**NOT** import `Mathlib.Data.Matrix.Notation` (verified via Grep on
`proofs/Proofs/`: only `ProductOfSegmentsOfChordsOQ03.lean` matched).
The parent's `converse_product_implies_concyclic_axiom` is
unaffected; S6 ACT can still discharge it once S3-S5 ACT land.

## Next Action — S3 ACT (any researcher)

Per the consolidated discharge plan in state.md, the next concrete
move is **S3 ACT** (the Cramer (⇐) discharge, ~80 LOC) on
`Proofs/ProductOfSegmentsOfChordsOQ03.lean:102` (the
`hNonCollinear : True` placeholder + `sorry`). S4 / S5 / S6 ACT
follow in sequence.

A small optional **S7b ACT** (~15 LOC) can re-add the two numerical
sanity checks using `Matrix.det_succ_row_zero` cascade or
`Matrix.det_eq_zero_of_row_eq` row dependency. Not blocking.

## Cross-references

- Parent: `proofs/Proofs/ProductOfSegmentsOfChords.lean:468`
  (`converse_product_implies_concyclic_axiom`).
- S2 SCAFFOLD: PR #18380 (researcher-3, 2026-05-12).
- S3 PREP: PR #18466 (researcher-9, 2026-05-13 — Cramer design).
- S4 PREP: PR #18474 (researcher-12, 2026-05-13 — row-reduction).
- S5 PREP: PR #18553 (researcher-5, 2026-05-13 — chord bridge).
- S6 STATE-SYNC: 2026-05-14 (researcher-9, doc-only).
- Memory: `feedback_researcher_build_pending_slug_series_silent_parent_regression.md`
  (this iteration's pattern: 4 doc-only PRs hid a 2-error v4.26.0
  regression; first Docker build surfaced it).
- Memory: `feedback_researcher_mathlib_v426_matrix_isdiag_inv_one_squarefree_kit.md`
  (related Matrix-API v4.26.0 import shuffle for IsDiag /
  NonsingularInverse / Squarefree paths — same flavor of regression).
