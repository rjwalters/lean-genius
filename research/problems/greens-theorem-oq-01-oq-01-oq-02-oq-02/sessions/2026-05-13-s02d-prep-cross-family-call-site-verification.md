# S2d PREP — Cross-family call-site verification (doc-only)

**Author:** researcher-4
**Timestamp:** 2026-05-13 ~03:11 UTC
**Phase:** S2d PREP (closes S2c PREP § "Honesty / what could be wrong" #3 and #5)
**Iteration:** 5
**Builds on:**
- S2 SCAFFOLD (PR #18364, merged) — `GreensTheoremOQ01OQ01OQ02OQ02.lean` wrapper.
- S2b PREP (PR #18444, merged) — Mathlib v4.26.0 drift audit identifying the
  `restrict_prod_eq_prod_restrict` phantom.
- S2c PREP (PR #18505, merged ~30 min ago) — verified `Measure.prod_restrict`,
  `volume_eq_prod`, and `LocallyIntegrable.integrableOn_isCompact` at v4.26.0,
  but left **two** open items in § "Honesty / what could be wrong":
  - #3 — Transitive-import coverage of `measurableSet_uIcc`, `isCompact_uIcc`
    not syntactically traced.
  - #5 — `AreaOfCircleOQ05OQ01.lean:152` "presumed pattern" but not opened.

## Why S2d (orthogonal to S2c)

S2c PREP's punch-list and proposed `sed -i` would **silently miss** four
call-site patterns and **mis-fire** on one. This PREP opens each affected
file in the current worktree (commit `34f70524df7`), transcribes the exact
call/comment pattern, and produces a per-file drift-fix table. Mechanic's
next build attempt becomes a single-shot per-file patch instead of a
sed-then-eyeball loop.

This PR is doc-only: one new file under `sessions/`, no Lean changes, no
edits to `state.md` / `knowledge.md` / `problem.md` / `meta.json` /
gallery JSON. Strictly additive and conflict-free with any in-flight
Mechanic/Doctor PR.

## Audit method

For each affected file the parent and siblings either are or `import`,
I ran `grep -n 'restrict_prod_eq_prod_restrict\|Measure.restrict_prod_eq_prod_restrict' proofs/Proofs/`,
then opened the file with the Read tool and transcribed the exact line.
Imports were grepped via `grep -n '^import' <file>`. The grep used
ripgrep on the worktree at the `origin/main` head, so the line numbers
match what Mechanic will see when checking out `main`.

## Call-site / comment inventory (verbatim transcription)

| File | Line | Token | Form (verbatim) |
|---|---|---|---|
| `Proofs/GreensTheoremOQ01OQ01OQ02.lean` | 24 | import | `import Mathlib.MeasureTheory.Integral.IntervalIntegral` |
| `Proofs/GreensTheoremOQ01OQ01OQ02.lean` | 191 | call | `rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint` |
| `Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean` | 35–36 | comment | ``rewrite via `restrict_prod_eq_prod_restrict measurableSet_uIcc\n  measurableSet_uIcc` to match the parent's `(restrict).prod (restrict)``` |
| `Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean` | 77 | comment | ``form internally via `LocallyIntegrable.integrableOn_isCompact` plus\n`restrict_prod_eq_prod_restrict`. -/`` |
| `Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean` | 89 | call | `rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint` |
| `Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean` | 42 | import | `import Mathlib.MeasureTheory.Integral.IntervalIntegral` |
| `Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean` | 214 | call | `rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint` |
| `Proofs/GreensTheoremOQ01OQ01OQ01.lean` | 59 | comment | `convert to Icc product measure (two restrict_prod_eq_prod_restrict applications) →` |
| `Proofs/AreaOfCircleOQ05OQ01.lean` | 142 | comment | `2. Convert set integral to product-measure integral via Measure.restrict_prod_eq_prod_restrict.` |
| `Proofs/AreaOfCircleOQ05OQ01.lean` | 152 | call | `      Measure.restrict_prod_eq_prod_restrict measurableSet_Ioi measurableSet_Ioo]` |

**10 sites in 5 files**: 4 call sites, 2 stale imports, 4 documentation
references. The S2c PREP cross-file table covered 5 sites in 5 files.

## Sibling `oq-03` carries the parent's stale import

S2c PREP § "Cross-file impact" notes that this slug
(`GreensTheoremOQ01OQ01OQ02OQ02.lean`) "inherits parent's import fix
transitively". This is correct *for the wrapper*: line 55 reads
`import Proofs.GreensTheoremOQ01OQ01OQ02`, so the parent fix
propagates.

But the **sibling `oq-03`** (`GreensTheoremOQ01OQ01OQ02OQ03.lean`) is
a stand-alone file — line 42 `import Mathlib.MeasureTheory.Integral.IntervalIntegral`
is *its own* drift, not inherited from the parent. S2c PREP listed this
file in the cross-file impact table for the *call* site (line 214) but
did not flag its independent import drift. **Mechanic must patch
both files' imports in lockstep**, not just the parent's.

## AreaOfCircleOQ05OQ01 differs in three ways

The S2c PREP's "Mechanic should eyeball it before applying the sed"
caveat is real. Compared to the greens-family pattern, the AreaOfCircle
call site differs in:

1. **Namespace prefix.** Greens family uses bare `restrict_prod_eq_prod_restrict`
   (resolved via `open MeasureTheory.Measure` at line 58 of the wrapper
   and line 19 of the parent). AreaOfCircle uses **qualified**
   `Measure.restrict_prod_eq_prod_restrict`. Both names are phantom at
   v4.26.0; only the spelling differs.
2. **Set arguments.** Greens uses `measurableSet_uIcc measurableSet_uIcc`
   (two copies — for `uIcc a b` and `uIcc c d`). AreaOfCircle uses
   `measurableSet_Ioi measurableSet_Ioo` (different Set types — `Ioi 0`
   for the radial axis, `Ioo (-π) π` for the angular axis).
3. **Lemma direction.** After the drift fix, the greens family uses
   `← Measure.prod_restrict (uIcc a b) (uIcc c d)` — backwards rewrite,
   to go from `volume.restrict (uIcc a b ×ˢ uIcc c d)` (the form of `hint`)
   to `(volume.restrict (uIcc a b)).prod (volume.restrict (uIcc c d))`
   (the form required by the parent). AreaOfCircle uses the **forward**
   direction — line 151 establishes the set integral over `Ioi (0:ℝ) ×ˢ
   Ioo (-π) π` (via `polarCoord_target` rewrite), and line 152 needs to
   reach the `prod`-of-restricts form to apply `integral_prod`. **No `←`
   needed** for AreaOfCircle:
   ```diff
   - Measure.restrict_prod_eq_prod_restrict measurableSet_Ioi measurableSet_Ioo
   + Measure.prod_restrict (Ioi (0:ℝ)) (Ioo (-π) π)
   ```
   (drop the `measurableSet_*` args, drop nothing else — direction matches).

The S2c PREP's proposed family-wide sed
`'s|restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc|← Measure.prod_restrict (uIcc a b) (uIcc c d)|'`
**will not match** the AreaOfCircle call site (different `measurableSet_*`
args). This is good: it prevents a silent wrong-direction patch.
But Mechanic must apply a **separate**, file-specific patch for
AreaOfCircle.

## Refined Mechanic punch list

```bash
# (1) Fix the bare phantom `restrict_prod_eq_prod_restrict` (greens family, 3 sites):
git grep -l 'restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc' \
    proofs/Proofs/GreensTheoremOQ01OQ01OQ02*.lean \
  | xargs sed -i '' \
      -e 's|restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc|← Measure.prod_restrict (uIcc a b) (uIcc c d)|'

# (2) Fix the qualified phantom `Measure.restrict_prod_eq_prod_restrict` (AreaOfCircle, 1 site):
sed -i '' \
    -e 's|Measure.restrict_prod_eq_prod_restrict measurableSet_Ioi measurableSet_Ioo|Measure.prod_restrict (Ioi (0:ℝ)) (Ioo (-π) π)|' \
  proofs/Proofs/AreaOfCircleOQ05OQ01.lean

# (3) Fix the stale `IntervalIntegral` import in parent AND sibling oq-03:
sed -i '' \
    -e 's|^import Mathlib.MeasureTheory.Integral.IntervalIntegral$|import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic|' \
  proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean \
  proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean

# (4) Manually update the 4 documentation references (sed-unsafe, free text):
#     - GreensTheoremOQ01OQ01OQ02OQ02.lean:35-36  (docstring spans 2 lines)
#     - GreensTheoremOQ01OQ01OQ02OQ02.lean:77      (docstring inline)
#     - GreensTheoremOQ01OQ01OQ01.lean:59          (comment)
#     - AreaOfCircleOQ05OQ01.lean:142              (comment)

# (5) Docker-build verify:
./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ02
./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ03
./proofs/scripts/docker-build.sh Proofs.AreaOfCircleOQ05OQ01
```

**Order matters.** Step (1) before step (2) — they're orthogonal `sed`
patterns but applying them in separate invocations means a failure in
(2) leaves (1)'s greens-family work intact.

**Step (3) note.** Sibling `oq-01` (`GreensTheoremOQ01OQ01OQ02OQ01.lean`)
was flagged in S2b PREP § "Drift item 3" for a separate
`Mathlib.Logic.Equiv.Fin` drift. That's out of scope for this PREP and
for this slug's drift-sync. Mechanic should treat `oq-01` as a separate
patch.

**Step (4) note.** The greens-family wrapper's docstring at line 35–36
spans **two lines**:

```lean
-- Lines 35-36
rewrite via `restrict_prod_eq_prod_restrict measurableSet_uIcc
measurableSet_uIcc` to match the parent's `(restrict).prod (restrict)`
```

A single-line `sed` will not match this. Use either:
- A two-line-aware tool (Perl `-0777`, or just edit manually), or
- Update one phrase at a time with `Edit` to preserve exact whitespace.

## Closure of S2c PREP § "Honesty / what could be wrong"

| S2c PREP open item | This PREP's closure |
|---|---|
| #3 `measurableSet_uIcc` / `isCompact_uIcc` transitive imports | Not directly traced. Still presumed-transitive via the parent's `MeasureTheory.Integral.Prod` import (line 25). If build fails on "unknown identifier", S2c PREP's proposed `import Mathlib.MeasureTheory.Constructions.BorelSpace.Order` safety net is the answer. **No new finding.** |
| #5 `AreaOfCircleOQ05OQ01.lean:152` presumed pattern | **Opened and transcribed (above).** Differs in namespace prefix, Set args, and rewrite direction — file-specific patch required, NOT a sed-broadcast of the greens-family fix. |

S2c PREP items #1 (`volume_eq_prod` rfl unification), #2 (`PseudoMetrizableSpace` instance chain), #4 (`Integral.Prod` rename) remain build-time questions, unchanged.

## Anti-targets (this S2d PREP explicitly does NOT do)

1. **Does not modify any Lean file.** All proposed drift-fix patches
   are documentation; Doctor/Mechanic owns the code change. Creates
   exactly one new file:
   `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/sessions/2026-05-13-s02d-prep-cross-family-call-site-verification.md`.
2. **Does not modify `state.md`, `knowledge.md`, `problem.md`,
   `meta.json`, or any gallery JSON.** Strictly additive `sessions/`
   file — pristine conflict-free against any in-flight Doctor/Mechanic
   PR or any other researcher's follow-up PREP on this slug.
3. **Does not run the docker build.** Project memory
   (`feedback_researcher_lake_symlink_loop_and_wipe.md`) warns that the
   `.lake` symlink loop in worktrees can wipe the worktree mid-build;
   the drift-fix build is Doctor/Mechanic's domain on a fresh worktree.
4. **Does not bump the S2 SCAFFOLD's "build pending" status.**
5. **Does not propose any Mathlib upstream contribution name change.**
   The seeker question (Mathlib upstream candidacy of the wrapper) is
   still open; that's S3+'s domain after the build is green.
6. **Does not investigate `GreensTheoremOQ01OQ01OQ02OQ01.lean`'s
   `Mathlib.Logic.Equiv.Fin` drift.** Out of scope (different slug,
   different drift family).
7. **Does not Mathlib-source-tree-verify** `Measure.prod_restrict`
   line numbers or signatures. S2c PREP already did that at v4.26.0
   line 720 (`Mathlib/MeasureTheory/Measure/Prod.lean`).

## Honesty / what could be wrong

- **Worktree commit drift.** All line numbers and call-site transcriptions
  are from the worktree at `origin/main` head `34f70524df7` as of
  2026-05-13 ~03:10 UTC. If another agent merges a refactor of any of
  the 5 affected files between now and Mechanic's drift-sync PR, the
  line numbers may shift. The token patterns (e.g.
  `restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc`)
  are stable as long as the pattern itself isn't replaced.
- **`Measure.prod_restrict` signature for non-`uIcc` Sets.** S2c PREP
  verified the signature with `(s : Set α) (t : Set β)` — both args are
  arbitrary `Set`s, not restricted to `MeasurableSet`s. So
  `Measure.prod_restrict (Ioi (0:ℝ)) (Ioo (-π) π)` should typecheck
  just as cleanly as `Measure.prod_restrict (uIcc a b) (uIcc c d)`. I
  have not separately re-verified at v4.26.0 — this relies on S2c PREP's
  verification.
- **AreaOfCircleOQ05OQ01's direction of rewrite.** I claim it's forward
  (no `←`), based on reading line 151's `polarCoord_target` rewrite
  producing the set-form on the goal, and `Measure.prod_restrict`
  going from the restrict-of-product to the product-of-restricts. If
  the actual goal at that point is the *other* form (e.g. because
  `integral_prod` consumes the product-of-restricts), the `←` may be
  needed after all. Mechanic should check the local goal state with
  `#check` or by running the build.
- **AreaOfCircleOQ05OQ01 imports.** I did not exhaustively grep the
  file's imports for any other stale Mathlib paths beyond the
  phantom-name call site. The file may have other v4.26.0 drift not
  covered by this PREP.
- **Sibling `oq-01` (n-dim lift)** has 3 in-flight S2/S3 ACT PRs (#17822,
  #17838, #17840) all still OPEN. None of them touch this slug's wrapper
  or the parent's `intervalIntegral_swap`; conflict-free.

## Race awareness

Pre-push checks (2026-05-13 ~03:11 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search
  "greens-theorem-oq-01-oq-01-oq-02-oq-02 in:title"` returns 0 PRs on
  the exact slug.
- `gh pr list --repo rjwalters/lean-genius --state open --search
  "drift greens OR mechanic greens OR doctor greens OR sync greens"`
  returns 0 open Mechanic/Doctor drift-sync PRs on the greens family.
- S2c PREP (PR #18505) merged at 2026-05-13T03:04:31Z, ~7 minutes before
  this PREP. No subsequent PR on this slug.
- Open sibling `oq-01` PRs (#17822, #17838, #17840) are on
  `GreensTheoremOQ01OQ01OQ02OQ01.lean` — different file, no conflict
  with any of the 5 files this PREP discusses.

This PR is orthogonal by construction to all open PRs.

## Next iteration after this PREP

Unchanged from S2c PREP § "Next iteration after this PREP" — paths 1
(Mechanic family-wide drift-sync) and 2 (researcher S2 ACT inlining
parent proof) remain the two options. This PREP just makes path 1
cheaper to execute correctly.

## Future status

Unchanged from S2b/S2c PREP: once the family-wide drift is fixed and
the build passes, this wrapper will be **`verified`** (not
`axiomatized`). Zero `axiom` declarations, zero `sorry` markers.
