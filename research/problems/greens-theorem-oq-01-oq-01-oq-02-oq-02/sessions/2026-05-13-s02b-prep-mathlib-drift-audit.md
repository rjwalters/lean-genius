# S2b PREP — Mathlib v4.26.0 API drift audit (doc-only)

**Author:** researcher-10
**Timestamp:** 2026-05-13 ~01:55 UTC
**Phase:** S2b PREP (between S2 SCAFFOLD and S3 verification)
**Iteration:** 3 (post-#18364)
**Builds on:** S2 SCAFFOLD (researcher-11, PR #18364, merged 2026-05-12 ~21:25 UTC; build status "pending")

## Why S2b (rather than S3)

The S2 SCAFFOLD (PR #18364) landed `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean`
with `Build status: pending` — see `sessions/2026-05-12-s02-scaffold.md` § Build status.
The next planned phase (S3) is a gallery `meta.json` entry that asserts
`status: verified, sorries: 0, axioms: 0`, which is only honest after the build
actually passes.

Before claiming S3 readiness, this PREP does a **static Mathlib v4.26.0 API
audit** against the wrapper file and its sole transitive import
`Proofs.GreensTheoremOQ01OQ01OQ02` (the parent). The audit identifies
three drift items that will cause the build to fail at the current pin
(`leanprover-community/mathlib4 @ v4.26.0`, commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). All three are mechanical to
fix; none reflect a mathematical error.

Doc-only PR — no Lean changes. Drift-fix patches are the appropriate
scope for Doctor/Mechanic across the affected family (5 files; see
§ "Cross-file impact"). Modifying the parent here would conflate slugs
and create cross-slug ownership ambiguity.

## Mathlib v4.26.0 pin reference

- `proofs/lean-toolchain`: `leanprover/lean4:v4.26.0`
- `proofs/lakefile.toml`: `mathlib @ rev = "v4.26.0"`
- `proofs/lake-manifest.json` resolves to commit
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

The audit below cites Mathlib v4.26.0 source by `?ref=v4.26.0` on
`github.com/leanprover-community/mathlib4` (i.e. the tag, equivalent to
the pinned commit).

## Drift item 1 — `restrict_prod_eq_prod_restrict` does not exist

### Where used (this slug)

`proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean:89`

```lean
rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint
```

### Audit finding

A literal-string search across `leanprover-community/*` shows **zero**
hits for `restrict_prod_eq_prod_restrict`:

```
$ gh api -X GET search/code -f 'q="restrict_prod_eq_prod_restrict"' --jq '.total_count'
24                # All 24 are in this very repo (rjwalters/lean-genius)
$ gh api -X GET search/code -f 'q="restrict_prod_eq_prod_restrict" org:leanprover-community' --jq '.total_count'
0
```

The 24 hits in `rjwalters/lean-genius` (the parent + 4 dependents + their
session docs) all cite a name that is not actually defined anywhere in
Mathlib v4.26.0 or master.

### Mathlib v4.26.0 replacement

`Mathlib/MeasureTheory/Measure/Prod.lean:720` (at tag `v4.26.0`):

```lean
theorem prod_restrict (s : Set α) (t : Set β) :
    (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t) := by
  ...
```

Two structural differences vs the phantom `restrict_prod_eq_prod_restrict`:

1. **No measurability hypotheses required.** The new lemma takes just the
   two sets; the parent's `measurableSet_uIcc measurableSet_uIcc` args
   are surplus.
2. **Direction.** The new `prod_restrict` rewrites `(μ.restrict s).prod
   (ν.restrict t)` → `(μ.prod ν).restrict (s ×ˢ t)`. The parent's
   intended direction (rewrite `hint : Integrable f (volume.restrict
   (uIcc a b ×ˢ uIcc c d))` to match the goal's product-of-restricts
   form) is the **reverse** direction, so the fix uses `← Measure.prod_restrict`.

### Proposed drift-fix patch (Doctor/Mechanic; NOT in this PR)

```diff
-  rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint
+  rwa [← Measure.prod_restrict (uIcc a b) (uIcc c d)] at hint
```

Caveats for the verifier:

- The `rwa` may also need a preceding step to unfold `volume` on
  `ℝ × ℝ` as `volume.prod volume`. Mathlib defines volume on a product
  type via `MeasureTheory.MeasureSpace` instance, which should be
  definitionally `volume.prod volume`. If `rwa` fails to unify, add
  `rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl]`
  or `simp only [Measure.volume_eq_prod]` before the `rwa`.
- The argument order to `Measure.prod_restrict` (which set is `s`, which
  is `t`) is fixed by which side of `×ˢ` the integrand lives on. The
  patch above passes `(uIcc a b)` first and `(uIcc c d)` second to match
  the existing `(uIcc a b ×ˢ uIcc c d)` order; this should be correct
  but is build-validation-gated.

## Drift item 2 — Parent import path stale (`Mathlib.MeasureTheory.Integral.IntervalIntegral`)

### Where used

`proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean:24` (the parent):

```lean
import Mathlib.MeasureTheory.Integral.IntervalIntegral
```

### Audit finding

`gh api .../contents/Mathlib/MeasureTheory/Integral/IntervalIntegral.lean?ref=v4.26.0`
returns 404. The module was restructured into a directory:

```
Mathlib/MeasureTheory/Integral/IntervalIntegral/
├── Basic.lean
├── ContDiff.lean
├── DerivIntegrable.lean
├── FundThmCalculus.lean
├── IntegrationByParts.lean
├── LebesgueDifferentiationThm.lean
├── Periodic.lean
├── Slope.lean
└── TrapezoidalRule.lean
```

A past build log confirms the failure mode for this exact import:

```
.loom/logs/researcher-12-greens-s3-build.log:
✖ [2/98] Running Mathlib.MeasureTheory.Integral.IntervalIntegral
error: no such file or directory (error code: 2)
  file: .../Mathlib/MeasureTheory/Integral/IntervalIntegral.lean
✖ Proofs.GreensTheoremOQ01OQ01OQ02
  bad import 'Mathlib.MeasureTheory.Integral.IntervalIntegral'
```

### Proposed drift-fix patch (Doctor/Mechanic; NOT in this PR)

```diff
-import Mathlib.MeasureTheory.Integral.IntervalIntegral
+import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
```

This is the parent file (`GreensTheoremOQ01OQ01OQ02.lean`), NOT the
wrapper this slug owns. The wrapper itself imports `Proofs.GreensTheoremOQ01OQ01OQ02`
which is the correct local import; the wrapper inherits the broken
Mathlib path transitively.

If `Basic` doesn't pull in `integral_integral_swap` / `intervalIntegral_swap`
prerequisites, the parent may need additional imports — e.g.
`Mathlib.MeasureTheory.Integral.Prod` (used by the parent for
`MeasureTheory.integral_integral_swap`; this line is at parent:25 and
appears to be at the correct path already). Verify on first build attempt.

## Drift item 3 — Sibling `oq-01` import `Mathlib.Logic.Equiv.Fin` also stale

### Audit finding (informational, not in this slug's scope)

The same past build log shows the sibling `GreensTheoremOQ01OQ01OQ02OQ01.lean`
fails on:

```
✖ Proofs.GreensTheoremOQ01OQ01OQ02OQ01
  bad import 'Mathlib.Logic.Equiv.Fin'
```

This file is owned by sibling slug `greens-theorem-oq-01-oq-01-oq-02-oq-01`
(`oq-01` not `oq-02`); flagged here only so Doctor/Mechanic can bundle
fixes if doing family-wide drift-sync. Not in this PR's scope.

## Cross-file impact (drift-fix scope)

`restrict_prod_eq_prod_restrict` appears in **5 local Lean files**:

| File | Line | Owner slug | Build status if drift unfixed |
|---|---|---|---|
| `Proofs/GreensTheoremOQ01OQ01OQ02.lean` | 191 | `greens-theorem-oq-01-oq-01-oq-02` (parent) | Build error: unknown identifier |
| `Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean` | 89 | **this slug** | Build error (inherits) |
| `Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean` | 214 | sibling oq-03 | Build error |
| `Proofs/AreaOfCircleOQ05OQ01.lean` | 152 | `area-of-circle-oq-05-oq-01` | Build error |
| `Proofs/GreensTheoremOQ01OQ01OQ01.lean` | 59 | sibling oq-01 (parent-of-parent) | Comment only — no compile impact |

The Doctor/Mechanic drift-sync PR should patch **lines 191, 89, 214, 152**
in lockstep (single `git grep -l 'restrict_prod_eq_prod_restrict' proofs/Proofs/`
+ sed), then re-run the docker build to validate the direction (`← Measure.prod_restrict`)
and argument unification.

`Mathlib.MeasureTheory.Integral.IntervalIntegral` import: needs sweep
across `proofs/Proofs/` separately — same single-import-line drift fix.

## Anti-targets (this S2b PREP explicitly does NOT do)

1. **Does not modify any Lean file.** All proposed drift-fix patches
   are documentation; Doctor/Mechanic owns the actual code change. This
   keeps the PR doc-only and avoids cross-slug edit ownership
   ambiguity (the parent file is a different slug from this wrapper).
2. **Does not modify `state.md`, `knowledge.md`, `problem.md`, or
   `meta.json` /any gallery JSON.** Strictly additive
   `sessions/2026-05-13-s02b-prep-mathlib-drift-audit.md` file —
   pristine conflict-free against any in-flight Doctor/Mechanic PR.
3. **Does not run the docker build.** The build itself is 25-45 min
   and is gated by Doctor/Mechanic per project convention (see
   `feedback_researcher_lake_symlink_loop_and_wipe.md` in memory:
   `.lake` symlink loop can wipe worktree mid-build).
4. **Does not bump S2 SCAFFOLD's "build pending" status.** Even if
   the drift-fix is mechanical, the wrapper file builds only if the
   parent builds, and the parent fix is cross-slug. S3 verification
   stays pending.
5. **Does not propose a Mathlib upstream contribution name change.**
   The seeker question (does the wrapper merit Mathlib upstream?) is
   still open; this PREP does not address it.

## Honesty / what could be wrong

- I have **not** verified by running the build that `← Measure.prod_restrict
  (uIcc a b) (uIcc c d)` is the exactly correct replacement. The
  signature `(s : Set α) (t : Set β)` is fixed at v4.26.0:720, and
  the direction `(μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)`
  is the published form; the `←` and the `volume = volume.prod volume`
  defeq must be checked at build time. The replacement may need a
  surrounding `simp only` to handle the volume unfolding.
- The third drift item (`Mathlib.Logic.Equiv.Fin` in sibling oq-01) is
  cited from `.loom/logs/researcher-12-greens-s3-build.log`. If that
  log is stale (>1 week old), the import path may have been fixed in
  the meantime. Verify with a current build attempt.
- I have **not** checked whether the parent file's
  `MeasureTheory.integral_integral_swap` (cited in `problem.md` /
  `knowledge.md` of the parent slug) is still at the same path/name.
  This is the parent slug's S1 OBSERVE concern, not this wrapper's.
- The audit's "build never passed" hypothesis is unfalsifiable from
  static inspection alone. The parent is marked `status: verified` in
  `src/data/proofs/greens-theorem-oq-01-oq-01-oq-02/meta.json`, but
  per `feedback_researcher_seeker_misplaced_wiedijk.md` and similar
  memory entries, gallery `status: verified` is set by the merge author,
  not by an automated build gate. The S2 SCAFFOLD's
  `sessions/2026-05-12-s02-scaffold.md` explicitly notes "Build pending"
  (it did not attempt the build) and gives the convention precedent of
  other recent "build-pending" OQ-02 family PRs (#17822, #17838, #17840,
  #18210). Mechanic-as-build-gate is the project norm; this PREP simply
  pre-stages the audit so the next build attempt has a clear punch list.

## Race awareness

Pre-push checks (2026-05-13 ~01:55 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search "greens-theorem-oq-01-oq-01-oq-02-oq-02 in:title"`
  returns 0 PRs on the **exact** `oq-02-oq-02` slug. (Three open PRs
  on sibling `oq-02-oq-01` exist: #17822, #17838, #17840 — different
  file, different slug.)
- `git branch -r | grep "greens-theorem-oq-01-oq-01-oq-02-oq-02"`
  returns 0 branches on this exact slug.
- No `audit/sync-greens-theorem-oq-01-oq-01-oq-02-oq-02*` or
  `doctor/*` branches in flight (manual check).

This PR is orthogonal by construction to any concurrent in-flight ACT
on sibling oq-01 (different file path, different slug), and to any
Doctor/Mechanic drift-sync (separate Lean-file edits, this PR is
docs-only with new file path
`research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/sessions/2026-05-13-s02b-prep-mathlib-drift-audit.md`).

## Next iteration after this PREP

S3 cannot proceed until the parent file builds. Two paths:

1. **Doctor/Mechanic picks up drift-sync** (preferred). They bundle the
   `restrict_prod_eq_prod_restrict` → `← Measure.prod_restrict` fix +
   the `IntervalIntegral` → `IntervalIntegral.Basic` import fix into a
   single tracker-style PR across 4-5 affected files. Re-run docker
   build. Update meta.json status for affected slugs.
2. **A subsequent researcher iteration ships S2c ACT** on this slug
   alone — modifies *only* `GreensTheoremOQ01OQ01OQ02OQ02.lean` (the
   wrapper) and inlines a stand-alone `prod_restrict`-based proof that
   does not depend on the parent. This decouples the slug from the
   parent's drift risk but duplicates ~100 lines of the parent's sign
   analysis. Not preferred — option 1 is cheaper and family-wide.

In either path, after the build is green:

- S3 finalization: update
  `src/data/research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02.json`
  with `status: completed, axiomCount: 0, sorryCount: 0`, link to the
  built file.
- Update `state.md` Phase: `S3 ACT (build-verified)`.
- Discuss Mathlib upstream candidacy in `knowledge.md` § Mathlib
  upstream — the wrapper is a small ergonomic improvement of the kind
  Mathlib welcomes; suggested target file
  `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` near
  `MeasureTheory.integral_integral_swap`.

## Future status

This wrapper, once the drift is fixed and the build passes, will be
**`verified`** (not `axiomatized`): the proof is a 5-line reduction to
the parent, the parent itself uses only standard Mathlib API, and the
wrapper introduces zero `axiom` declarations and zero `sorry` markers
(per the S2 SCAFFOLD file content at lines 78-90).
