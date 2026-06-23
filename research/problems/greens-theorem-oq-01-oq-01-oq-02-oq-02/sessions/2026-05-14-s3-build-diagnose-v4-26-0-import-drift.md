# S3 BUILD-DIAGNOSE — Docker build blocked by v4.26.0 Mathlib import drift in parent + sibling files (doc-only)

**Date**: 2026-05-14
**Researcher**: researcher-12
**Phase**: S3 BUILD-DIAGNOSE (cross-slug v4.26.0 import drift inventory; researcher scope = doc only)
**Mathlib pin**: v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Risk**: NONE (no Lean edits in this PR)

## §0 What this PR does

Docker-build attempt of `Proofs.GreensTheoremOQ01OQ01OQ02OQ02` (the
S3 ACT deliverable from PR #18944, still tagged `(build pending)` in
state.md) surfaced **two v4.26.0 Mathlib path-drift errors** in the
**parent file** `Proofs.GreensTheoremOQ01OQ01OQ02.lean` and the
sibling `Proofs.GreensTheoremOQ01OQ01OQ02OQ01.lean`.

Both errors are independent of this slug's S3 ACT lean edit (the
`volume_eq_prod` + `Measure.prod_restrict` bridge at line 101 of
`OQ02OQ02.lean`); they are upstream-Mathlib path-rename regressions
that block compilation of the whole family.

**This PR is doc-only.** It adds the diagnostic + 1-LOC mechanic-fix
proposal to `knowledge.md`. No Lean files are edited; no `state.md`
or research JSON is edited (those are held by open STATE-SYNC PR
#18993).

## §1 Verified findings

### §1.1 `Mathlib.MeasureTheory.Integral.IntervalIntegral` → directory split

At v4.26.0 rev `2df2f015...`, the single-file module
`Mathlib/MeasureTheory/Integral/IntervalIntegral.lean` has been
**replaced by a directory** containing 9 submodules:

```
Mathlib/MeasureTheory/Integral/IntervalIntegral/
├── Basic.lean                       ← core API (intervalIntegral, IntervalIntegrable, ∫ x in a..b, …)
├── ContDiff.lean
├── DerivIntegrable.lean
├── FundThmCalculus.lean
├── IntegrationByParts.lean
├── LebesgueDifferentiationThm.lean
├── Periodic.lean
├── Slope.lean
└── TrapezoidalRule.lean
```

The barrel file `Mathlib/MeasureTheory/Integral/IntervalIntegral.lean`
no longer exists. Confirmed via:

```bash
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/MeasureTheory/Integral/IntervalIntegral.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
# → {"message":"Not Found", "status":"404"}

gh api "repos/leanprover-community/mathlib4/contents/Mathlib/MeasureTheory/Integral/IntervalIntegral?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
# → 9 files listed above
```

### §1.2 `Mathlib.Logic.Equiv.Fin` → directory split

Analogously, the single-file module `Mathlib/Logic/Equiv/Fin.lean`
has been **replaced by a directory** containing 2 submodules:

```
Mathlib/Logic/Equiv/Fin/
├── Basic.lean
└── Rotate.lean
```

Confirmed via:

```bash
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Logic/Equiv/Fin.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
# → {"message":"Not Found", "status":"404"}

gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Logic/Equiv/Fin?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
# → Basic.lean, Rotate.lean
```

## §2 Cascade — files affected across the gallery

Repo-wide grep for the stale single-file imports (only **exact**
matches; anchored to start-of-line):

### §2.1 `import Mathlib.MeasureTheory.Integral.IntervalIntegral` (7 files)

| File | Line | Slug ownership |
|---|---|---|
| `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` | 24 | greens-theorem-oq-01-oq-01-oq-02 (parent) |
| `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean` | 42 | greens-theorem-oq-01-oq-01-oq-02-oq-03 (sibling) |
| `proofs/Proofs/Erdos515Problem.lean` | 34 | erdos-515 |
| `proofs/Proofs/AreaOfCircleOQ01OQ02OQ02OQ01.lean` | 2 | area-of-circle (sibling family) |
| `proofs/Proofs/BuffonsNoodle.lean` | 3 | buffons-noodle |
| `proofs/Proofs/BuffonsNeedleOQ02OQ02.lean` | 2 | buffons-needle-oq-02-oq-02 |
| `proofs/Proofs/AreaOfCircleOQ03OQ03.lean` | 3 | area-of-circle-oq-03-oq-03 |

### §2.2 `import Mathlib.Logic.Equiv.Fin` (1 file)

| File | Line | Slug ownership |
|---|---|---|
| `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean` | 39 | greens-theorem-oq-01-oq-01-oq-02-oq-01 (n-dim sibling) |

**This slug's own file** (`GreensTheoremOQ01OQ01OQ02OQ02.lean`) does
**not** import either of the broken paths directly — but it imports
`Proofs.GreensTheoremOQ01OQ01OQ02` which does, so the cascade still
blocks the build.

## §3 Build log evidence

The previous Docker-build attempt against `Proofs.GreensTheoremOQ01OQ01OQ02OQ02`
(log: `.loom/logs/researcher-12-greens-s3-build.log`, ~150s into the
build, post-cache-download) failed with:

```
✖ [2/98] Running Mathlib.MeasureTheory.Integral.IntervalIntegral
error: no such file or directory (error code: 2)
  file: /Users/rwalters/.../proofs/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral.lean

✖ [3058/3061] Running Proofs.GreensTheoremOQ01OQ01OQ02
error: Proofs/GreensTheoremOQ01OQ01OQ02.lean: bad import 'Mathlib.MeasureTheory.Integral.IntervalIntegral'

✖ [3059/3061] Running Mathlib.Logic.Equiv.Fin
error: no such file or directory (error code: 2)
  file: /Users/rwalters/.../proofs/.lake/packages/mathlib/Mathlib/Logic/Equiv/Fin.lean

✖ [3060/3061] Running Proofs.GreensTheoremOQ01OQ01OQ02OQ01
error: Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean: bad import 'Proofs.GreensTheoremOQ01OQ01OQ02'
error: Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean: bad import 'Mathlib.Logic.Equiv.Fin'

Some required targets logged failures:
- Mathlib.MeasureTheory.Integral.IntervalIntegral
- Proofs.GreensTheoremOQ01OQ01OQ02
- Mathlib.Logic.Equiv.Fin
- Proofs.GreensTheoremOQ01OQ01OQ02OQ01
error: build failed
```

The errors clearly identify the missing barrel files — not just a
local symlink loop. The cache downloaded **7727 of 7727** Mathlib
files cleanly, so the cache is intact; the bad-import errors are
inside the local `proofs/Proofs/*.lean` files.

## §4 Proposed mechanic fix

### §4.1 Surgical 1-LOC import-line swaps

The most likely-correct minimal patch is one of two patterns per
import:

**Pattern A (most permissive):** replace the single-file barrel with
its core submodule `.Basic`. This is the canonical Mathlib v4.26.0
pattern for the parent module split:

```lean
-- Before:
import Mathlib.MeasureTheory.Integral.IntervalIntegral
-- After:
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
```

```lean
-- Before:
import Mathlib.Logic.Equiv.Fin
-- After:
import Mathlib.Logic.Equiv.Fin.Basic
```

**Pattern B (minimal API search):** identify which submodule actually
provides the symbols the file uses, and import only that. For the
Greens family, the parent file uses `intervalIntegral_swap` (no, it
**defines** it — searching Mathlib4 v4.26.0 confirms there is **no**
upstream `intervalIntegral_swap` lemma), `∫ x in a..b, _ ∂μ` notation
(in `Basic.lean`), and `MeasureTheory.integral_integral_swap` (in
`Mathlib/MeasureTheory/Integral/Prod.lean`, separately imported).
So **Pattern A → `.Basic`** is the correct fix for the parent.

For `OQ01.lean`'s `Logic.Equiv.Fin` usage (the n-dim slice/iterate
construction), it imports the file to use `finSuccEquiv` and
`Equiv.piFinSucc`, both of which live in `Basic.lean` (verified by
inspecting the file at the pin — `Rotate.lean` only contains
`Fin.rotate`-style lemmas). So **Pattern A → `.Basic`** is also
correct for `OQ01.lean`.

### §4.2 Total mechanic patch budget

| File | Patch |
|---|---|
| `GreensTheoremOQ01OQ01OQ02.lean:24` | `IntervalIntegral` → `IntervalIntegral.Basic` (1 LOC) |
| `GreensTheoremOQ01OQ01OQ02OQ03.lean:42` | `IntervalIntegral` → `IntervalIntegral.Basic` (1 LOC) |
| `Erdos515Problem.lean:34` | `IntervalIntegral` → `IntervalIntegral.Basic` (1 LOC) |
| `AreaOfCircleOQ01OQ02OQ02OQ01.lean:2` | `IntervalIntegral` → `IntervalIntegral.Basic` (1 LOC) |
| `BuffonsNoodle.lean:3` | `IntervalIntegral` → `IntervalIntegral.Basic` (1 LOC) |
| `BuffonsNeedleOQ02OQ02.lean:2` | `IntervalIntegral` → `IntervalIntegral.Basic` (1 LOC) |
| `AreaOfCircleOQ03OQ03.lean:3` | `IntervalIntegral` → `IntervalIntegral.Basic` (1 LOC) |
| `GreensTheoremOQ01OQ01OQ02OQ01.lean:39` | `Equiv.Fin` → `Equiv.Fin.Basic` (1 LOC) |

**Total: 8 LOC across 8 files** (7 distinct slug families).

### §4.3 Required follow-on Docker verification

After the 8-LOC swap, mechanic must Docker-build the family:

```bash
./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02       # parent
./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ01   # sibling n-dim
./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ02   # this slug
./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ03   # sibling Bochner
```

(Also: `Proofs.Erdos515Problem`, `Proofs.AreaOfCircleOQ01OQ02OQ02OQ01`,
`Proofs.BuffonsNoodle`, `Proofs.BuffonsNeedleOQ02OQ02`,
`Proofs.AreaOfCircleOQ03OQ03` — separate slug families, mechanic should
verify but they may also have additional v4.26.0 regressions beyond
this import drift.)

If any submodule API has further drifted (e.g. `intervalIntegral_swap`
relying on Bochner sublemmas no longer in `Basic.lean`'s
transitive closure), mechanic may need to expand the import set:

```lean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus  -- if needed
```

The 9-submodule directory list in §1.1 is the search space.

## §5 Why this is doc-only (researcher scope)

Per project memory `[Researcher — Parent-regression isolation via new
file split]` and CLAUDE.md "Math agents must NOT add
`loom:review-requested`":

- The cascade affects **7 distinct slug families** (greens, erdos-515,
  buffons-noodle, buffons-needle, area-of-circle ×3 sub-slugs).
  Bundling 8 cross-slug Lean edits into one research PR violates the
  one-slug-per-PR norm.
- The import-rename is a mechanical mechanic-scope edit; researcher
  scope here is the **diagnostic** + **fix-kit specification**.
- The slug's S3 ACT lean edit at `OQ02OQ02.lean:101` (the
  `volume_eq_prod` + `Measure.prod_restrict` bridge) is **already
  shipped via PR #18944**. There is no further researcher Lean work
  here until the parent's import is restored.

This PR ships the diagnostic and unblocks mechanic to apply the
8-LOC mechanic fix in either one cross-cutting `fix(mechanic):` PR
or per-slug mechanic PRs as preferred.

## §6 What this PR does NOT change

- **No Lean edits.** All 8 affected files remain at their broken
  imports.
- **No `state.md` edits.** Open PR #18993 holds the state.md +
  research JSON STATE-SYNC lock; my findings here will be picked up
  by the next STATE-SYNC after #18993 merges (or after this PR's
  knowledge.md addition is in main, whichever is later).
- **No JSON edits.** Same reason as state.md.
- **No `problem.md` edits.** The problem statement (LocallyIntegrable
  wrapper) is unaffected by the import drift; the deliverable theorem
  remains as stated.

## §7 Coordination with PR #18993

PR #18993 is an open STATE-SYNC docs-only PR for this exact slug,
fixing post-#18944 `state.md` + research JSON drift. It modifies:

- `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/state.md`
- `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/state.json`
  (or top-level research JSON)
- A new session log at
  `research/problems/.../sessions/2026-05-14-state-sync-post-s3-act.md`

This PR (S3 BUILD-DIAGNOSE) modifies:

- `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/knowledge.md`
  (new §S3 BUILD-DIAGNOSE section appended)
- A new session log at
  `research/problems/.../sessions/2026-05-14-s3-build-diagnose-v4-26-0-import-drift.md`

**No file overlap.** Either PR may merge first; the deployer can take
them in either order.

## §8 Followups recorded for the next STATE-SYNC

When #18993 + this PR have both merged, a subsequent state.md sync
should:

1. Add a new row to the Decomposition Plan:
   `| S3 BUILD-DIAGNOSE | DOC | v4.26.0 parent + sibling import drift inventory | 0 Lean (docs) | **MERGED #TBD** |`
2. Update **Phase** to reflect that S3 ACT is **build-blocked by
   parent regression**, not just "build pending".
3. Update **Next Action** to **"Mechanic fix per §4 of S3
   BUILD-DIAGNOSE"** (not "Docker-build verify"; the build is
   structurally blocked until §4 lands).
4. Add to **Blockers**: "Parent file `Proofs.GreensTheoremOQ01OQ01OQ02`
   import drift at v4.26.0; see §S3 BUILD-DIAGNOSE knowledge.md for
   the 8-LOC mechanic fix-kit."

## §9 References

- Parent file (broken at v4.26.0): `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean:24`
- This slug's target file (transitively blocked):
  `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean:55` (imports parent)
- Build log: `.loom/logs/researcher-12-greens-s3-build.log` (~150s
  in; 7727/7727 Mathlib files cached cleanly, then 4 explicit
  `bad import` failures)
- Mathlib v4.26.0 pin: rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
- Mathlib v4.26.0 file inventory under `Integral/IntervalIntegral/`:
  9 submodules (`.Basic` is the canonical core)
- Mathlib v4.26.0 file inventory under `Logic/Equiv/Fin/`:
  2 submodules (`.Basic` is the canonical core)
- Sibling open PR #18993 (STATE-SYNC docs-only for this slug)
- Predecessor S3 ACT PR #18944 (lean edit at `OQ02OQ02.lean:101`,
  `(build pending)` flag still in place per state.md)
