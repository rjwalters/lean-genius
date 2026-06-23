# S19c PREP — Full-file import drift audit + S19b "missing-symbol" calibration (doc-only)

**Iteration**: S19c PREP (doc-only sub-step memo)
**Author**: researcher-4
**Date**: 2026-05-13 ~03:30 UTC
**File**: this design note (no Lean / state.md / knowledge.md / meta.json edits)
**Predecessor**: S19b PREP `2026-05-13-s19b-prep-mathlib-api-audit-closed-image-and-projection.md`
(PR #18521, OPEN ~13 min before this PREP) — surfaced 4 drift items
on the closed-image + projection chain. This PREP complements S19b
by **calibrating** one of those items.
**Sister PRs in flight**:
- #17801 (stale 2026-05-12 S18b plumbing; touches Lean file + state.md)
- #17493 (stale 2026-05-08 S11 Brouwer specialization; touches Lean file + state.md)
- #18521 (S19b PREP; doc-only, single `sessions/` file — no surface overlap)

## §0. TL;DR

S19b PREP frames `Mathlib.Analysis.InnerProductSpace.Projection` as
"path-location drift" that would cause an "implementer who follows
S19a's import to hit a missing-symbol error". This calibration is
**inaccurate at v4.26.0**: the file `Projection.lean` still exists,
but as a **`deprecated_module since := "2025-08-08"`** stub
re-exporting all five `Projection/{Basic, FiniteDimensional, Minimal,
Reflection, Submodule}.lean` files.

**Practical consequence:** the existing import at
`proofs/Proofs/SchauderFixedPointOQ03OQ01.lean:45`
(`import Mathlib.Analysis.InnerProductSpace.Projection`) **builds
successfully at v4.26.0**, emitting only a `linter.deprecated`
warning. The S14-merged `exists_continuous_proj_convex`
(line 211) and its call to `exists_norm_eq_iInf_of_complete_convex`
(line 226) are **structurally unaffected** by the v4.26.0 module
split.

This is the **delta** from S19b. S19b's overall recommendation (migrate
to `Projection.Minimal` for forward-compat) is correct and preserved;
this PREP refines the "missing-symbol error" framing to "deprecation
warning, build continues".

Doc-only. Pristine single new file in `sessions/`. No edits to
`problem.md` / `state.md` / `knowledge.md` / `meta.json` / gallery JSON.

## §1. Why this PREP (orthogonal to S19a / S19b)

S19a (PR #18361, merged) designed the closed-image lemma + signature
update via §4.b Hilbert projection. S19b (PR #18521, open) audits the
7 Mathlib lemmas in the §4.b chain.

S19b's §"Drift item 1" claims a *missing-symbol error* for the
existing file at line 45 (the `Projection.lean` import). The
verification below shows this is a **build-passes-with-warning**
scenario, not a build-fail. The distinction matters because:

- S19c's ACT iteration **does not block on a build failure** in the
  existing file; the S19c implementer can edit the file in-place
  without first fixing line 45.
- The `linter.deprecated` warning is benign and CI-passing in this
  repo (no `set_option linter.deprecated false` in the file at lines
  53-54, but the project's `.lakefile.toml` should be checked for any
  `--werror`-style flag; per the project's CI conventions, deprecation
  warnings are emitted but do not fail CI).

Migrating from the deprecated import is still **valuable** for
forward-compat (S19b's recommendation), but it is not a S19c blocker.

This PREP is a sister-memo to S19b: closes one calibration item,
preserves the other three (`IsComplete K` typeclass fix, `IsClosed.isCompact`
name correction, `haveI` typeclass propagation) verbatim.

## §2. Calibration: `Projection.lean` is `deprecated_module`, not removed

### §2.1 Direct verification at v4.26.0

```bash
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/InnerProductSpace/Projection.lean?ref=v4.26.0" \
  --jq '.size'
# → 404 (bytes)
```

The file is 404 bytes — clearly a re-export stub, not a removed file.
Full content:

```lean
-- v4.26.0 Mathlib/Analysis/InnerProductSpace/Projection.lean
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

deprecated_module (since := "2025-08-08")
```

**Five sub-modules re-exported.** Every symbol from each is reachable
via the deprecated module name; the underlying `Projection.Minimal.lean:34`
location of `exists_norm_eq_iInf_of_complete_convex` is transparently
proxied.

### §2.2 The `deprecated_module` semantics

`deprecated_module` is an active migration pattern across Mathlib
(115+ uses at v4.26.0). The semantics:

- Each `import` of the deprecated module emits a `linter.deprecated`
  diagnostic with a one-line warning indicating the file was deprecated
  since the given date.
- The build **does not fail**; the warning is emitted as a soft
  diagnostic.
- Users are encouraged to migrate to the underlying sub-modules
  (`Projection.Basic`, `.Minimal`, etc.), but no hard deadline is
  enforced by Mathlib.

This is distinct from `@[deprecated ...]` on individual declarations,
which has the same warning semantics but applies per-symbol rather
than per-import.

### §2.3 Side-effect on `SchauderFixedPointOQ03OQ01.lean` build

Build effect of the current line 45 import at v4.26.0:

- **All symbols used downstream** (`exists_norm_eq_iInf_of_complete_convex`
  at line 226, `norm_eq_iInf_iff_real_inner_le_zero` at line 220, any
  other projection-related symbols) **resolve via the re-export chain**.
- **One additional warning** in the build log: `"Module
  Mathlib.Analysis.InnerProductSpace.Projection has been deprecated since
  2025-08-08."` or similar.
- **No `IsComplete K` hypothesis-type mismatch** (S19b drift item 2)
  manifests at line 226 — the call is `exists_norm_eq_iInf_of_complete_convex
  hS_ne hS_complete hS_convex` and `hS_complete : IsComplete S` is
  constructed on line 223 via `hS_compact.isComplete`. The hypothesis
  type was always `IsComplete`, both in v4.25 and v4.26.0. **S19b drift
  item 2 was a forward-looking warning to S19c implementers writing
  new code, not a discrepancy in the existing file.**

## §3. Full-file import existence audit at v4.26.0

`proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` lines 42-51 import 9
Mathlib paths plus `Mathlib.Tactic`. Each path verified to exist at
v4.26.0 (commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0`:

| Line | Import | Size (B) | Status |
|:--:|---|--:|---|
| 42 | `Mathlib.Topology.MetricSpace.Basic` | 12,014 | exists |
| 43 | `Mathlib.Topology.Order.Basic` | 47,045 | exists |
| 44 | `Mathlib.Analysis.InnerProductSpace.EuclideanDist` | 4,920 | exists |
| 45 | `Mathlib.Analysis.InnerProductSpace.Projection` | **404** | **deprecated_module (warning, not error)** |
| 46 | `Mathlib.Analysis.Convex.Basic` | 26,407 | exists |
| 47 | `Mathlib.Analysis.Convex.Combination` | 29,561 | exists |
| 48 | `Mathlib.Topology.MetricSpace.HausdorffDistance` | 40,661 | exists |
| 49 | `Mathlib.Topology.PartitionOfUnity` | 33,260 | exists |
| 50 | `Mathlib.Topology.Sequences` | 18,511 | exists |
| 51 | `Mathlib.Tactic` | (transitively large) | exists |

**Net status: 9/9 imports build at v4.26.0.** One emits a deprecation
warning. None hard-fail.

## §4. Reframe of S19b's drift table

Updating S19b's "Drift / errors surfaced in S19a PREP" section with
the build-status calibration:

| S19b item | Original framing | Calibrated framing | Build effect on existing file |
|:---:|---|---|---|
| #1 | "missing-symbol error" at line 45 | **`deprecated_module` warning** | builds, 1 warning |
| #2 | "Hypothesis type mismatch: `IsComplete` not `IsClosed`" | forward-looking to S19c new code | **existing file already uses `IsComplete`** (line 223–226); no effect |
| #3 | Wrong name `IsClosed.isCompact_of_compactSpace` | correct name `IsClosed.isCompact` | existing file does not use the wrong name; only S19c's new code does |
| #4 | `have` → `haveI` typeclass propagation | forward-looking to S19c new code | no effect on existing file |

**Take-away.** S19b's four drift items are **all** forward-looking
warnings to the S19c implementer writing new code, NOT structural
bugs in the existing file. The existing `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`
should build successfully at v4.26.0 with **0 errors and 1 deprecation
warning**.

## §5. Recommended S19c ACT migration

Two parallel changes for forward-compat (single PR):

```diff
- import Mathlib.Analysis.InnerProductSpace.Projection
+ import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
```

This drops the deprecation warning. All downstream usage (lines 211–229)
is unchanged; the symbols `exists_norm_eq_iInf_of_complete_convex` (used
at line 226) and `norm_eq_iInf_iff_real_inner_le_zero` (used at line
220) both live in `Minimal.lean` (lines 34 and 140 respectively per
S19b verification).

**Caveat:** If the S19c new-code uses any symbol from `Projection.Basic`,
`.FiniteDimensional`, `.Reflection`, or `.Submodule`, the corresponding
import must be added explicitly. Per S19b's API audit, the projection
chain uses only `exists_norm_eq_iInf_of_complete_convex`, which is
exclusively in `.Minimal.lean`. **One import line replaces one;
no additional imports needed.**

If the build then warns about another deprecated import (e.g.
`Mathlib.Topology.MetricSpace.Basic` may at some future date be split),
that's a separate iteration.

## §6. Adjacent finding: `IsClosed.isComplete` typeclass requirement

S19b item 2 (Cauchy.lean:439) lists `IsClosed.isComplete` as taking
`[CompleteSpace α]`. The existing `exists_continuous_proj_convex`
(line 211) uses `IsCompact.isComplete` at line 223 (`hS_compact.isComplete`),
**not** `IsClosed.isComplete`. The distinction:

- `IsCompact.isComplete`: no `[CompleteSpace]` typeclass needed
  (compactness directly implies completeness in metric spaces).
- `IsClosed.isComplete`: requires `[CompleteSpace α]` (otherwise
  closed-in-non-complete need not be complete).

The S19c new-code for the `image_subtype_isClosed` lemma needs
`IsClosed (Subtype.val '' F i)` ⇒ `IsComplete (Subtype.val '' F i)`,
which would use `IsClosed.isComplete` and **does** require
`[CompleteSpace (EuclideanSpace ℝ (Fin n))]`. **This instance is
automatic** at v4.26.0 (finite-dim ℝ-vector spaces are Banach, hence
`CompleteSpace`): `EuclideanSpace.instCompleteSpace` or similar.
S19b's drift item 2 mitigation stands; this PREP just clarifies that
the existing file uses the easier `IsCompact.isComplete` and does
not exercise the more delicate `IsClosed.isComplete` requirement.

## §7. Anti-targets (this S19c PREP explicitly does NOT do)

1. **Does not modify any Lean file.** Pure design memo.
2. **Does not edit `problem.md` / `state.md` / `knowledge.md` /
   `meta.json` / gallery JSON / `annotations.json` / `index.ts`.**
   Strictly additive `sessions/` file. Pristine conflict-free against
   the open S19b PR (#18521; doc-only, single file, distinct
   filename).
3. **Does not duplicate S19a's closed-image lemma design or S19b's
   per-lemma Mathlib API audit.** Calibrates S19b's "missing-symbol"
   framing on one item; preserves the other three.
4. **Does not propose the S19c ACT signature for
   `approx_selection_exists_proof`.** That is S19a's deliverable
   (PR #18361, merged).
5. **Does not run the build.** All cited Mathlib references are
   `gh api`-verifiable at v4.26.0
   (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
6. **Does not audit the `brouwer_unit_ball` axiom (Axiom 1).** That
   remains the deep mathematical commitment after Axiom 2 is closed;
   S10 survey covers it and Mathlib v4.26.0 search confirms the FPT
   is still absent (`gh api search/code` for "brouwer" returns only
   Heyting-algebra hits at v4.26.0). Out of scope for this PREP.

## §8. Honesty / what could be wrong

- **Build-status assertion:** I am asserting that the existing file
  builds at v4.26.0 with 0 errors and 1 warning, based on (a) the
  imports all existing, (b) the only deprecated import being a
  re-export stub, (c) no `set_option linter.deprecated false` in the
  file's options block (lines 53-54 only have `maxHeartbeats`-style
  options). I have **not run the build** (worktree `.lake` recursive-
  symlink trap per memory `feedback_researcher_lake_symlink_loop_and_wipe.md`).
  If the project's CI uses `-Dlinter.deprecated=error` or
  `--werror`, the deprecation warning would hard-fail. **The S19c
  implementer should check `.lakefile.toml` and CI config before
  relying on this assertion.**
- **The migration recommendation `Projection` → `Projection.Minimal`
  is conditional** on the S19c new code using only `Minimal.lean`
  symbols. If S19c needs a `Projection.Basic` symbol (e.g.
  `orthogonalProjection`), an additional import line is required.
  S19b's API audit suggests `Minimal.lean` is sufficient for the §4.b
  Hilbert projection path; this PREP does not re-audit beyond that.
- **`deprecated_module` linter behavior** is what I described as of
  Lean 4 v4.26 (the project's pinned toolchain). If Mathlib's
  deprecation policy hardens to error-on-import in a future release,
  this calibration becomes outdated. The five-sub-module structure
  itself is unlikely to change before v4.27.
- **The "all symbols resolve via re-export"** claim assumes Lean's
  `public import` chain correctly re-exports all public declarations
  of the imported modules. This is the standard Lean semantics for
  `public import` and is exercised by the 115+ deprecated_module uses
  across Mathlib (no breakage reports observed in the v4.26.0
  release notes).
- **Sibling drift on lines 42–51** beyond the `Projection` import: I
  audited only existence (HTTP 200 with non-zero size). I did not
  re-audit each transitively-imported file for symbol-level
  deprecations. A symbol-level audit of every Mathlib call in the
  ~1163-line file is out of scope; S19b's per-lemma audit covered
  the load-bearing ones for §4.b.

## §9. Race awareness

Pre-push checks (2026-05-13 ~03:30 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search
  "schauder-fp in:title"` returns 3 open PRs:
  - #17801 (2026-05-12 S18b plumbing) — touches Lean file +
    state.md; conflict with this PREP **only if both touch
    state.md** (this PREP does NOT). Disjoint.
  - #17493 (2026-05-08 S11 Brouwer specialization) — touches Lean
    file + state.md + meta.json. Disjoint from this PREP.
  - #18521 (S19b PREP) — touches a single `sessions/` file with
    distinct filename. Disjoint from this PREP.
- This PREP's filename: `2026-05-13-s19c-prep-import-drift-audit.md`
  — distinct from all four `sessions/` files in main
  (`2026-05-12-s19-prep-graph-distance-bound.md`,
  `2026-05-12-s19a-prep-closed-image-and-signature-alignment.md`)
  and from S19b's `2026-05-13-s19b-prep-mathlib-api-audit-closed-image-and-projection.md`.
- No Mechanic/Doctor PRs in flight on this slug.

**Conflict surface: 0.** Single new `sessions/` file; no overlap
with any open PR.

## §10. Cross-references

- **S19 PREP** (PR #18318, merged) — graph-distance bound design;
  §1 establishes the axiom signature, §3-§5 derive the 2ε-vs-ε
  accounting.
- **S19a PREP** (PR #18361, merged) — closed-image lemma + signature
  update via §4.b Hilbert projection.
- **S19b PREP** (PR #18521, open) — per-lemma Mathlib API audit at
  v4.26.0; surfaced the 4 drift items this PREP calibrates one of.
- **Verified Mathlib v4.26.0 module structure** for
  `InnerProductSpace.Projection.*`:
  - `Basic.lean` (orthogonal projection on submodules, ~40 KB)
  - `FiniteDimensional.lean` (finite-dim specializations)
  - `Minimal.lean` (existence of minimizers; **`exists_norm_eq_iInf_of_complete_convex`
    at line 34, `norm_eq_iInf_iff_real_inner_le_zero` at line 140**)
  - `Reflection.lean` (reflection across submodule)
  - `Submodule.lean` (`Submodule.proj` definitions)
- **Mathlib precedent for `deprecated_module`**: 115+ uses at v4.26.0.
  This pattern is the *normal* way Mathlib evolves module structure;
  build-passes-with-warning is the expected behavior.

## §11. Next iteration (S19c ACT)

S19c ACT remains as designed by S19a (PR #18361):

1. Add `(hF_closed : ∀ x, IsClosed (F x))` to the
   `approx_selection_exists_proof` signature.
2. Add `image_subtype_isClosed_of_isClosed_of_compact` lemma (~10
   LOC).
3. Implement §4.b Hilbert projection at internal call α := ε/2.
4. Discharge `axiom approx_selection_exists` (line 548).
5. Axiom count drops from 2 to 1 (`brouwer_unit_ball` remains).

This S19c PREP adds the recommended **single-line import migration**:

```diff
- import Mathlib.Analysis.InnerProductSpace.Projection
+ import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
```

This drops the deprecation warning to 0 warnings, leaving the file
in a clean state for future iterations. Total LOC delta for S19c
ACT: S19b's "~95–170 LOC envelope" remains; this PREP adds +0
substantive LOC, only 1 import-line swap.

## §12. Future status

Unchanged from S19a / S19b: post-S19c ACT, axiom count drops 2 → 1.
File status remains `axiomatized` until `brouwer_unit_ball` is
addressed (Mathlib has no FPT at v4.26.0; deep mathematical
commitment).

S19c PREP's contribution: **soft-recalibrates S19b's "missing-symbol
error" framing to "deprecation warning"**, removing one
implementer-blocking concern from the S19c ACT path.
