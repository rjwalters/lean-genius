# S12 PREP — S5-region mechanic-ready kit for `ThreeSquares.lean`

**Author**: researcher-9
**Date**: 2026-05-14 (UTC)
**Mode**: PREP / doc-only
**Phase**: ACT (S11/S10D shipped in PR #19048, build pending on S5-region)
**Scope**: Convert the 9-error S5-region build blocker (lines 756–864 of
`proofs/Proofs/ThreeSquares.lean`) documented in PR #19048's body into a
cluster-classified, Mathlib v4.26.0 pin-verified mechanic kit so a single
Mechanic / Doctor PR can unblock the file in one Docker iteration.

This PREP is **conflict-free** with the two open PRs:

| Open PR | File touched | This PREP file touched |
|---|---|---|
| #19048 (me, S10D ACT) | `ThreeSquares.lean`, `state.md`, `lagrange-four-squares-oq-01-oq-02.json` | none of these |
| #19026 (researcher-12, STATE-SYNC) | `lagrange-four-squares-oq-01-oq-02.json` | none of these |

This PREP touches ONLY a new file `sessions/2026-05-14-s12-prep-s5-mechanic-kit.md`.

## Why a kit prep, not a fix

Per `feedback_researcher_build_blocker_mechanic_kit_prep_pattern.md`: when a
claimed slug is BUILD-BLOCKER with `N ≥ 4` errors and no open mechanic/doctor PR,
the researcher's productive move is to write a cluster-classified mechanic kit
(pin-verified Mathlib APIs, file:line refs, ordered fix sequence, acceptance
criteria) — the `≤ 3-error rule` blocks shipping a researcher fix PR. Here `N = 9`.

The S10D ACT in PR #19048 is unrelated to the S5-region blockers (the new
content at lines 1593–1659 elaborates cleanly per `.loom/logs/researcher-9-lagrange4sq-s10d-build2.log`).
The S5 region has been build-pending since the S5 ACT in PR #16987 (2026-05-08);
six subsequent sessions (S6–S11/S10D) have been "build pending" because each was
arithmetic-only and orthogonal to the S5 measure-theoretic core. Unblocking
this region lets the full file build clean for the first time since the v4.26.0
pin landed.

## Mathlib v4.26.0 pin

Manifest SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (verified in
`proofs/lake-manifest.json:"mathlib"."rev"`). All bearer lookups below were
verified via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`
at 2026-05-14 ~23:30 UTC.

## Baseline error inventory

From `.loom/logs/researcher-9-lagrange4sq-s10d-build2.log` (Docker build of the
PR #19048 ACT branch on 2026-05-14 ~12:00 UTC; the S5-region failures predate
the S10D additions and reproduce on a clean S10D-prep baseline as well):

```
error: Proofs/ThreeSquares.lean:760:65: Type mismatch
error: Proofs/ThreeSquares.lean:765:13: Unknown constant `Matrix.det_toLin'`
error: Proofs/ThreeSquares.lean:756:64: unsolved goals
error: Proofs/ThreeSquares.lean:790:48: Type mismatch
error: Proofs/ThreeSquares.lean:792:4:  Type mismatch
error: Proofs/ThreeSquares.lean:813:10: No goals to be solved
error: Proofs/ThreeSquares.lean:816:4:  unsolved goals
error: Proofs/ThreeSquares.lean:849:6:  No goals to be solved
error: Proofs/ThreeSquares.lean:864:23: Unknown constant `EuclideanSpace.real_norm_sq_eq`
```

Plus six `simp` argument unused warnings (lines 801, 820, 821, 1007, 1444,
1448, 1580, 1584, 1587) and two deprecated-name warnings (1164, 1312) — out of
scope for this kit (warnings, not errors).

## Cluster classification

### Cluster A — `Real.sqrt_mul_self` vs `Real.mul_self_sqrt` direction (3 errors)

**Errors**: lines 760:65, 790:48, 792:4 — all type-mismatch.

**Root cause**: each site assigns a term `Real.sqrt_mul_self <h>` to a `have`
declaration of type `Real.sqrt x * Real.sqrt x = x`. At v4.26.0 (and in fact
since Mathlib's name-convention canonicalisation), the lemma `Real.sqrt_mul_self`
has signature `√(x * x) = x` (the *outside* `sqrt` of an inner `x*x`), while
the lemma matching the `have` declaration's RHS is `Real.mul_self_sqrt`
(`√x * √x = x`, the *outside* product of two `sqrt x` terms).

**Pin-verified at v4.26.0**: `Mathlib/Data/Real/Sqrt.lean:134,138`:

```lean
-- line 134: matches the have's RHS pattern
theorem mul_self_sqrt (h : 0 ≤ x) : √x * √x = x

-- line 138: NOT what these sites need
theorem sqrt_mul_self (h : 0 ≤ x) : √(x * x) = x
```

**Fix (3 LOC, surgical rename)**:

```diff
- have h_sqRd : Real.sqrt (R / d) * Real.sqrt (R / d) = R / d := Real.sqrt_mul_self hRd
+ have h_sqRd : Real.sqrt (R / d) * Real.sqrt (R / d) = R / d := Real.mul_self_sqrt hRd
```

at line 760, and the two parallel sites at lines 790 and 792.

### Cluster B — `Matrix.det_toLin'` → `LinearMap.det_toLin'` namespace (1 error)

**Error**: line 765:13 — Unknown constant.

**Root cause**: the lemma lives in `namespace LinearMap` at v4.26.0, not
`namespace Matrix`. The proof goal at line 756 is
`LinearMap.det (dirichletScale d R) = R ^ (3/2 : ℝ) / d` with
`dirichletScale d R := Matrix.toLin' (dirichletScaleMatrix d R)` (line 745).
The needed rewrite has type `LinearMap.det (Matrix.toLin' f) = Matrix.det f`,
i.e. exactly `LinearMap.det_toLin'`.

**Pin-verified at v4.26.0**: `Mathlib/LinearAlgebra/Determinant.lean:211`:

```lean
@[simp]
theorem det_toLin' (f : Matrix ι ι R) : LinearMap.det (Matrix.toLin' f) = Matrix.det f := by
  simp only [← toLin_eq_toLin', det_toLin]
```

The surrounding `namespace LinearMap` block runs from approximately line ~160
through ~250 (verifiable by `gh api …` content scan; the
nearby `LinearMap.det_toMatrix`, `LinearMap.det_toMatrix'`, `LinearMap.det_toLin`
sibling lemmas confirm the namespace).

**Fix (1 LOC, surgical rename)**:

```diff
- rw [Matrix.det_toLin', Matrix.det_diagonal, Fin.prod_univ_three]
+ rw [LinearMap.det_toLin', Matrix.det_diagonal, Fin.prod_univ_three]
```

at line 765.

### Cluster C — `EuclideanSpace.real_norm_sq_eq` → `EuclideanSpace.norm_sq_eq` rename (1 error)

**Error**: line 864:23 — Unknown constant.

**Root cause**: the `EuclideanSpace.real_norm_sq_eq` specialisation to ℝ was
removed at v4.26.0; the surviving cousin is `EuclideanSpace.norm_sq_eq`
(the polymorphic `[RCLike 𝕜]` version) at
`Mathlib/Analysis/InnerProductSpace/PiL2.lean:145`. The two differ in that the
removed `real_norm_sq_eq` returned `‖x‖^2 = ∑ i, x i ^ 2` (squared values
without the norm) whereas the surviving `norm_sq_eq` returns
`‖x‖^2 = ∑ i, ‖x i‖^2` (squared norms). For `x : EuclideanSpace ℝ (Fin 3)`,
`x i : ℝ`, so `‖x i‖ = |x i|` (via `Real.norm_eq_abs` at
`Mathlib/Analysis/Normed/Group/Real.lean`) and `|x i|^2 = x i^2` (via `sq_abs`).

**Pin-verified at v4.26.0**: `Mathlib/Analysis/InnerProductSpace/PiL2.lean:145`:

```lean
theorem EuclideanSpace.norm_sq_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ x
```

`Real.norm_eq_abs` pin-verified at `Mathlib/Analysis/Normed/Group/Real.lean`
(currently alive at v4.26.0; per
`feedback_researcher_mathlib_v426_complex_norm_eq_abs_simp_only_norm_num_drift.md`
the **Complex** `norm_eq_abs` is the one with `simp only` drift — the **Real**
variant works fine in `rw`).

**Fix (3 LOC, rename + post-bridge)**:

```diff
- have h_norm_sq : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
-   rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
+ have h_norm_sq : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
+   rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three,
+       Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
+   simp only [sq_abs]
```

at line 864. (Three `Real.norm_eq_abs` rewrites because `rw` is left-to-right
and the goal has three independent `‖x i‖` occurrences after
`Fin.sum_univ_three`. `simp only [sq_abs]` then collapses `|x i|^2 → x i^2`.)

If the Mechanic prefers a more idiomatic form, an equivalent 2-LOC variant is:

```lean
have h_norm_sq : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]
```

(plain `simp` rather than `simp only`; this avoids the `simp only`/`norm_num`
ambient-list lookup drift documented for `Complex.norm_eq_abs`, and `Real.norm_eq_abs`
is not affected by that drift since it is not deprecated). Mechanic discretion.

### Cluster D — `field_simp` over-closure: trailing `ring` no-ops (2 errors)

**Errors**: lines 813:10, 849:6 — "No goals to be solved".

**Root cause**: at v4.26.0, `field_simp` is more aggressive (now internally
invokes `ring_nf` after denominator-clearing). Both call sites used the v4.25.x
idiom `field_simp; ring` where `field_simp` cleared denominators and `ring`
closed the resulting polynomial identity. At v4.26.0 `field_simp` alone closes
the polynomial identity, so the trailing `ring` has no goal to act on.

**Fix (2 LOC, surgical removal)**:

Lines 810–813 (the `show ... by` block inside the outer `rw`):

```diff
  rw [show v 0 ^ 2 / R + v 1 ^ 2 / (R / d) + v 2 ^ 2 / (R / d)
        = (v 0 ^ 2 + d * v 1 ^ 2 + d * v 2 ^ 2) / R by
      field_simp
-     ring]
+     ]
```

Lines 847–849:

```diff
  rw [e1, e2, e3]
  field_simp
- ring
```

**Robustness option**: if a future Mathlib bump backs off the `field_simp`
aggression, prefer `field_simp <;> ring` instead of bare `field_simp`; this is
a no-op when `field_simp` closes the goal and falls back to `ring` otherwise.
Per Mathlib idiom, this is the safest invocation. **Mechanic should prefer
`field_simp <;> ring` over bare `field_simp` removal** for forward-compat:

```diff
  rw [show v 0 ^ 2 / R + v 1 ^ 2 / (R / d) + v 2 ^ 2 / (R / d)
        = (v 0 ^ 2 + d * v 1 ^ 2 + d * v 2 ^ 2) / R by
-     field_simp
-     ring]
+     field_simp <;> ring]
```

```diff
  rw [e1, e2, e3]
- field_simp
- ring
+ field_simp <;> ring
```

Net LOC delta: −2 lines.

### Cluster E — Cascade unsolved-goals (2 errors, no direct fix needed)

**Errors**: lines 756:64, 816:4 — "unsolved goals".

**Root cause**: line 756:64 is the closing `:=` of the
`dirichletScale_det` theorem signature; the goal stays open because clusters A
(line 760) and B (line 765) leave the proof partial. Line 816:4 is the start
of the second `·` bullet of `dirichletEllipsoid_eq_image`'s `constructor`; the
goal stays open because cluster D at line 813 leaves the first bullet partial.

**Both errors dissolve when clusters A, B, D are fixed.** No edit needed.
Verify by Docker re-build after the 6 surgical edits land.

## Ordered fix sequence (leaf → structural)

Apply edits in this order to maximise the chance that a single Docker iter is
clean. Each step's Lean line numbers reference the pre-edit baseline (so
Mechanic should apply each independently, not as a single sed pass that shifts
lines):

1. **D-a** (line 813): remove trailing `ring` from the inner `show ... by`
   block inside the `rw` at lines 810–813 (or use `field_simp <;> ring` per
   robustness option).
2. **D-b** (line 849): remove trailing `ring` (or use `field_simp <;> ring`).
3. **A-1** (line 760): `Real.sqrt_mul_self` → `Real.mul_self_sqrt`.
4. **A-2** (line 790): same rename.
5. **A-3** (line 792): same rename.
6. **B** (line 765): `Matrix.det_toLin'` → `LinearMap.det_toLin'`.
7. **C** (line 864): `EuclideanSpace.real_norm_sq_eq` → `EuclideanSpace.norm_sq_eq`
   + bridge `rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]; simp only [sq_abs]`
   (or the equivalent `simp [Real.norm_eq_abs, sq_abs]` form).

After all 7 edits, the cluster-E cascade errors at lines 756 and 816 should
dissolve.

## LOC budget

| Cluster | Edits | Net LOC |
|---|---|---|
| A | 3 rename | 0 (in-place) |
| B | 1 rename | 0 (in-place) |
| C | 1 rename + 2 bridge lines | +2 |
| D | 2 line removals (or `<;> ring` consolidation) | −2 (or 0) |
| **Total** | **7 surgical edits** | **0 to +2 LOC** |

7 surgical edits, 9 errors gone, 0–2 net LOC change. Trivial mechanic PR.

## Acceptance criteria

The mechanic PR is complete iff:

1. `./proofs/scripts/docker-build.sh Proofs.ThreeSquares` produces 0 errors
   in lines 750–870 (the S5 region targeted by this kit).
2. No new errors introduced outside the S5 region (i.e., S10D content at
   1593–1659 still elaborates clean per `.loom/logs/researcher-9-lagrange4sq-s10d-build2.log`).
3. The full file builds clean modulo strategic-sorry warnings on
   `needs_four_iff_excluded` (line 1864, expected) — i.e., one `declaration uses 'sorry'`
   warning and the previously documented simp-arg-unused warnings (lines 801,
   820, 821, 1007, 1444, 1448, 1580, 1584, 1587).
4. Net LOC delta on `proofs/Proofs/ThreeSquares.lean` is ≤ +2.

## Out-of-kit scope (do NOT bundle into Mechanic PR)

The following appear in the same build log as warnings, but the
`feedback_researcher_build_blocker_mechanic_kit_prep_pattern.md` discipline
recommends warnings be left for a separate hygiene pass:

- **Deprecated name warnings** (lines 1164, 1312): `ZMod.natCast_zmod_eq_zero_iff_dvd`
  → `ZMod.natCast_eq_zero_iff`; `le_or_lt` → `le_or_gt`. Trivial; defer to a
  separate hygiene PR or include in a later research session.
- **Simp argument unused warnings** (lines 801, 820, 821, 1007, 1444, 1448, 1580, 1584, 1587):
  spurious `Matrix.cons_val_succ`, `Matrix.cons_val_fin_one`, etc. in `simp`
  argument lists. Out of scope.

## Sequencing options

**Option A (preferred)**: Wait for PRs #19048 (S10D ACT) and #19026 (STATE-SYNC)
to merge, then a Mechanic / Doctor agent picks up the kit and ships the
7-edit fix.

**Option B**: Mechanic ships immediately on top of `origin/main`. Then when
#19048 merges, the new S10D content at 1593–1659 elaborates clean (verified
independently in build2 log); the kit's S5-region edits live at 760–864
and have no overlap with the S10D edit zone.

**Option C**: Researcher (this session) overlays PR #19048 via
`gh pr diff 19048 | git apply` and Docker-verifies the kit, then ships an
**in-PR overlay** (`feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`).
Out of scope here because the ≤ 3-error researcher fix rule blocks shipping
the 7-edit kit as a researcher PR.

**Recommendation**: Option A or B; both work. Mechanic decides based on PR
backlog state when picking up.

## Honesty / scope guarantees

* **No Lean edits** in this PREP PR. `proofs/Proofs/ThreeSquares.lean` is
  untouched.
* **No `state.md` / `problem.md` / JSON edits.** This PR ONLY adds the file
  `research/problems/lagrange-four-squares-oq-01-oq-02/sessions/2026-05-14-s12-prep-s5-mechanic-kit.md`.
* **All cluster-A/B/C bearer line numbers verified via direct `gh api`** at
  SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (pinned manifest revision;
  see `proofs/lake-manifest.json`).
* **Cluster D root cause hypothesis** (`field_simp` over-closure at v4.26.0)
  is not Docker-verified in this PREP; recommended Mechanic flow includes
  Docker iteration after applying step D-a as a safety check.
* **No open PR overlap.** This PREP file (a new `sessions/` entry) does not
  overlap with PR #19048's or PR #19026's diff scopes.
