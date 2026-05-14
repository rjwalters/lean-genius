# S5b ACT — parent-file repair (4 surgical fixes, build verified)

**Date**: 2026-05-14
**Researcher**: researcher-9
**Phase**: ACT (build verification pending → see §3 for outcome)
**Path**: parent-file repair only (does NOT include S2 ACT proof body paste-in — preserved in
`2026-05-13-s5a-prep-mathlib-regression-discovery-and-proof-draft.md` §3 for next session)

## 0. TL;DR

Apply four Mathlib v4.26.0 surgical fixes to restore build of `eTranscendental.lean`
and `ETranscendentalOQ03.lean` on origin/main. Three were diagnosed in S5a §1;
the fourth (line-152 direction error in `IsFractionRing.isAlgebraic_iff` use)
surfaced only after Fix #1 unblocked the namespace lookup and Lean re-elaborated
past the original first-error site. Each fix is demonstrably one-line; the
bundle uses standard Mathlib re-imports, a project-local lemma already in tree
(`e_irrational`), and one `.mp` → `.mpr` direction flip. Per
`feedback_researcher_parent_file_build_unblocker_inpr_pattern.md`, this falls
under the "in-PR one-line unblocker" pattern even though four sites are touched
across two files, because the bundle is logically a single Mathlib API drift
repair.

Net effect on origin/main:
- `eTranscendental.lean` builds (was 9 errors)
- `ETranscendentalOQ03.lean` builds (was 1 error blocking on line 118)
- No new axioms, no new theorems, no proof-content drift
- Unblocks S5c (next-session S2 ACT proof body paste-in, axiom count 2 → 1)

## 1. The four surgical fixes

### Fix #1: `eTranscendental.lean` — add `Mathlib.RingTheory.Localization.Integral` import

**Symptom**: 8 sites at lines 151, 164, 183, 198, 212, 214, 224, 228 all error with
`Unknown constant IsFractionRing.isAlgebraic_iff`.

**Root cause**: The lemma `IsFractionRing.isAlgebraic_iff` lives at
`Mathlib/RingTheory/Localization/Integral.lean:139` at pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. The file `eTranscendental.lean`
imports `Mathlib.RingTheory.Algebraic.Basic` but not
`Mathlib.RingTheory.Localization.Integral`. In an earlier Mathlib version the
lemma was reachable transitively through `Algebraic.Basic`, but a Mathlib
refactor moved it into `Localization.Integral` (which depends on `Algebraic.Basic`,
not the reverse) and broke the transitive path.

**Fix** (1 line, line 2):
```diff
 import Mathlib.RingTheory.Algebraic.Basic
+import Mathlib.RingTheory.Localization.Integral
 import Mathlib.Analysis.SpecialFunctions.ExpDeriv
```

**Verification of the import target**: pinned-rev source at line 139 has the
expected signature:
```lean
theorem isAlgebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] {x : C} :
    IsAlgebraic A x ↔ IsAlgebraic K x
```
inside `namespace IsFractionRing` (declared earlier in the same file). Resolves
to the fully-qualified name `IsFractionRing.isAlgebraic_iff` at all 8 call sites.

### Fix #2: `eTranscendental.lean` line 225 — `isAlgebraic_algebraMap (1 : ℚ)` → `isAlgebraic_one`

**Symptom**: type mismatch on `isAlgebraic_algebraMap (1 : ℚ)`. The call is
trying to produce `IsAlgebraic ℚ (1 : ℝ)` but `isAlgebraic_algebraMap (1 : ℚ)`
has the literal type `IsAlgebraic ℚ (algebraMap ℚ ℝ 1)`, which is not
definitionally `IsAlgebraic ℚ (1 : ℝ)` in v4.26.0 (the `algebraMap ℚ ℝ 1 = 1`
fact is `propEq` but the elaborator wants `defEq` here, and the auto-`simp`
that bridged it in older Mathlib has been retired).

**Fix** (1 line, line 225):
```diff
-  have h1 : IsAlgebraic ℚ (1 : ℝ) := isAlgebraic_algebraMap (1 : ℚ)
+  have h1 : IsAlgebraic ℚ (1 : ℝ) := isAlgebraic_one
```

**Verification**: `isAlgebraic_one` is at
`Mathlib/RingTheory/Algebraic/Basic.lean:141` (pinned rev), declared as
`theorem isAlgebraic_one [Nontrivial R] : IsAlgebraic R (1 : A) := by
  exact isAlgebraic_algebraMap 1`. So semantically the same proof; the
upstream version handles the `(1 : R)` vs `algebraMap R A 1` mismatch with
its own elaborator-friendly variant.

### Fix #3: `ETranscendentalOQ03.lean` line 118 — `irrational_exp_iff.mpr ...` → `e_irrational`

**Symptom**: `Unknown identifier 'irrational_exp_iff.mpr'`.

**Root cause**: `Mathlib.Data.Real.Irrational` is now a `deprecated_module`
alias re-exporting `Mathlib.NumberTheory.Real.Irrational` (per the
`deprecated_module (since := "2025-10-13")` declaration at the top of the
deprecated file). The new home file at pinned rev contains no `irrational_exp_iff`
lemma — the lemma was upstream-removed during the move, not just relocated.
Confirmed by full-tree search at pin: zero hits for `irrational_exp_iff`.

**Fix** (2 changes: 1-line import + 1-line use-site):

Import (line 7):
```diff
 import Mathlib.Tactic
+import Proofs.eTranscendental
```

Use site (line 118 → 119 after import shift):
```diff
 theorem e_liouvilleWith_two : LiouvilleWith 2 (exp 1) :=
-  irrational_liouvilleWith_two _ (irrational_exp_iff.mpr (by norm_num : (1 : ℚ) ≠ 0))
+  irrational_liouvilleWith_two _ e_irrational
```

**Verification**: `e_irrational` is at `proofs/Proofs/eTranscendental.lean:167`
(project-local), with signature
`theorem e_irrational : Irrational (Real.exp 1) := e_irrational_axiom`.
Same type as `irrational_exp_iff.mpr (by norm_num : (1 : ℚ) ≠ 0)` produced.

**Cascade ordering**: Fix #3 depends on Fix #1+#2 because
`Proofs.eTranscendental` must compile for the import to resolve. The fix-stack
order is therefore enforced: build `eTranscendental.lean` first (Fix #1+#2),
then `ETranscendentalOQ03.lean` (Fix #3 + import-of-fixed-eTranscendental).

### Fix #4: `eTranscendental.lean` line 152 — `.mp` → `.mpr` direction flip

**Symptom**: After Fix #1 unblocked the namespace, the first Docker build
surfaced a new error:
```
error: Proofs/eTranscendental.lean:152:74: Application type mismatch:
  halg has type IsAlgebraic ℚ (rexp 1)
  but is expected to have type IsAlgebraic ℤ ?m.17
  in (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp halg
```

This was masked from S5a because Lean stops at the first error in a file, and
S5a's build never got past the line-151 `Unknown constant` namespace failure
to elaborate line 152.

**Root cause**: The Mathlib v4.26.0 signature is
`IsAlgebraic A x ↔ IsAlgebraic K x` (with the ring `A` on the left, the
fraction field `K` on the right). So with `A = ℤ`, `K = ℚ`:
- `.mp : IsAlgebraic ℤ x → IsAlgebraic ℚ x` (ring → fraction field)
- `.mpr : IsAlgebraic ℚ x → IsAlgebraic ℤ x` (fraction field → ring)

The use at line 152 needs ℚ → ℤ to feed `e_transcendental : ¬IsAlgebraic ℤ`.
That is the `.mpr` direction; the code had `.mp`.

**Fix** (1 line, line 152):
```diff
 theorem e_transcendental_over_rationals : Transcendental ℚ (Real.exp 1) :=
-  fun halg => e_transcendental ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp halg)
+  fun halg => e_transcendental ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr halg)
```

**Why the other 7 `IsFractionRing.isAlgebraic_iff` sites in the same file are
correct**: Sites at lines 164, 198, 214, 228 already use `.mpr` for ℚ → ℤ
(consistent with v4.26.0 convention). Sites at lines 184, 213, 224 already use
`.mp` for ℤ → ℚ (also consistent). Direction-by-direction audit:

| Line | Input type      | Output needed   | Used  | v4.26.0 correct |
|------|-----------------|-----------------|-------|-----------------|
| 152  | IsAlgebraic ℚ   | IsAlgebraic ℤ   | `.mp` | **flip to `.mpr`** |
| 164  | IsAlgebraic ℚ   | IsAlgebraic ℤ   | `.mpr`| ✓ |
| 184  | IsAlgebraic ℤ   | IsAlgebraic ℚ   | `.mp` | ✓ |
| 198  | IsAlgebraic ℚ   | IsAlgebraic ℤ   | `.mpr`| ✓ |
| 213  | IsAlgebraic ℤ   | IsAlgebraic ℚ   | `.mp` | ✓ |
| 214  | IsAlgebraic ℚ   | IsAlgebraic ℤ   | `.mpr`| ✓ |
| 224  | IsAlgebraic ℤ   | IsAlgebraic ℚ   | `.mp` | ✓ |
| 228  | IsAlgebraic ℚ   | IsAlgebraic ℤ   | `.mpr`| ✓ |

So line 152 is the lone outlier. Most likely the file was committed with a
direction error that never surfaced because the file lived in a broken-build
state from some earlier Mathlib break and the section past line 151 was never
re-elaborated.

## 2. Race awareness

Pre-claim race check at 2026-05-14 ~04:00 UTC:
- 0 open PRs with `nth-root-irrational-oq-03 in:title`
- 0 open PRs with `eTranscendental in:title` or `ETranscendental in:title`
- 0 open `parent-file fix` PRs in the transcendental cluster
- Most recent merge: S5a PREP (PR #18978, 2026-05-14 03:03 UTC, researcher-12)

Branch: fresh `research/researcher-9-nth-root-<ts>` off origin/main
(2afb1b79c0a). Per `feedback_researcher_worktree_branch_lags_origin_main_iter_stale.md`,
the worktree was rebased before claim.

## 3. Build outcome

Docker build target: `Proofs.ETranscendentalOQ03` (which transitively builds
`Proofs.eTranscendental` per the Fix #3 import).

Build logs:
- `.loom/logs/researcher-9-nthroot-s5b-build.log` — first build after Fix #1+#2+#3,
  surfaced the line-152 direction error.
- `.loom/logs/researcher-9-nthroot-s5b-build2.log` — second build after adding Fix #4.

**Result**: `Build completed successfully (3071 jobs).`

Both `eTranscendental.lean` and `ETranscendentalOQ03.lean` now compile cleanly on
Mathlib v4.26.0 (pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). The only
remaining linter output is a deprecation warning on `Mathlib.Data.Real.Irrational`
(now a deprecation alias for `Mathlib.NumberTheory.Real.Irrational`); that
deprecation cleanup is out-of-scope for this repair PR.

Total Lean-file diff: +3 / −2 lines across the two files (excluding the new
`Proofs.eTranscendental` import in `ETranscendentalOQ03.lean`).

## 4. Scope discipline

This PR is **parent-file repair only**. Out of scope:

- **S2 ACT proof body paste-in**: the ~85-LOC drafted proof from S5a §3
  remains in the previous session note for next-session use. Bundling it
  here would inflate review surface for an unrelated concern (the parent-file
  repair stands on its own merit even if the S2 ACT proof body needed tactic
  adjustment under a Docker build).
- **Axiom count change**: `e-transcendental-oq-03/meta.json` axiomCount remains
  at its current value. The bundle-with-S2-ACT path would have decremented
  2 → 1; that decrement is deferred to the next research PR.
- **S5 ACT for `hermite_lindemann`**: still gated on Mathlib PR #28013 merge.
  S4c watch-loop cadence (24h check) inherited from prior sessions.

## 5. Cross-slug coordination

The Fix #1 pattern (`add import Mathlib.RingTheory.Localization.Integral` to
files using `IsFractionRing.isAlgebraic_iff`) may apply to other transcendence
slugs. Quick scan of project for additional sites:

```bash
grep -rn "IsFractionRing.isAlgebraic_iff" proofs/Proofs/ | \
  awk -F: '{print $1}' | sort -u
```

Result: only `proofs/Proofs/eTranscendental.lean` (8 sites). No cross-slug
breadcrumb from this fix.

The Fix #3 pattern (`irrational_exp_iff` removed → use project-local replacement)
is also single-site (only `ETranscendentalOQ03.lean:118`). Cross-slug grep:

```bash
grep -rn "irrational_exp_iff" proofs/Proofs/
```

Result: 0 hits after fix applied.

## 6. Honesty / what could be wrong

- **Docker build not yet completed at write-time.** Sections 1–5 are pre-build
  reasoning. The build outcome (§3) will be appended after the Docker exit.
- **Fix #1 hypothesis** (Mathlib refactor moved the lemma out of `Algebraic.Basic`'s
  transitive closure) is the simplest explanation but could be wrong; e.g., the
  lemma's signature could have been altered in a v4.26.0 PR, in which case the
  import alone is insufficient. The Docker build is the arbiter.
- **Fix #3** uses a project-local axiom replacement (`e_irrational` is defined
  via `e_irrational_axiom` at line 161). This **does not change the axiom count**
  on origin/main: the project already trusted `e_irrational_axiom` for its uses;
  this fix routes one more call site through the same axiom rather than through
  a Mathlib-side proof. If a future iteration wants stricter axiom hygiene,
  proving `e_irrational_axiom` directly (probably via `Liouville` infrastructure
  on the e continued fraction expansion) becomes a follow-up.
- **The build of `Proofs.ETranscendentalOQ03` may surface additional errors**
  not in S5a's inventory (e.g., line 118's downstream `e_liouvilleWith_two`
  usage in part III may have its own breakage). If so, this iteration ships
  as "build pending — parent-file blocker partially repaired" with the
  additional inventory.

## 7. What's next (S5c, next session)

After this S5b ACT merges:
1. Researcher claims slug; reads this note + S5a §3 (drafted proof body).
2. Inserts the ~85-LOC `rat_approx_bounded_den_finite` + `irrational_liouvilleWith_two`
   theorem at line 114 of `ETranscendentalOQ03.lean`.
3. Docker build verifies.
4. Decrement `axiomCount` 2 → 1 in `src/data/proofs/e-transcendental-oq-03/meta.json`
   (note: gallery entry may need creation if not already present per S1 OBSERVE).

Estimated S5c cost: 15-30 min including build.
