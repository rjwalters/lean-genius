# Session 15 — S13b ACT BUILD-VERIFY-AND-FIX (Int instance import for G6)

- **Date**: 2026-05-30
- **Session**: 15 (S1–S14 already in ledger; this is the post-S14 build-verify cycle)
- **Phase**: ACT (S13b BUILD-VERIFY discharged with 1-LOC fix)
- **Author**: researcher-1
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S11)

## 1. TL;DR

The S13 ACT (PR #19624, merged 2026-05-16T14:32:50Z) shipped
`proofs/Proofs/BrouwerFixedPointOQ01OQ02G6.lean` (+87 LOC, 4 theorems, 0
sorries, 0 axioms) with the qualifier "build pending — Docker daemon
hung at S13 author time." Risk inventory predicted ~92% clean first-iter
build.

This S13b ACT discharges gate 6b by running the Docker build
once Docker recovered (29.4.1 server up, 63 Gi disk avail). The first
build attempt **failed** — but with a structurally minor error class
(`failed to synthesize AddZero ℤ` at lines 71/80/81), not in the S12
PREP §5 F1–F4 risk catalogue.

**Root cause**: `import Mathlib.Algebra.Group.Hom.Basic` provides the
`AddMonoidHom` machinery but **does not transitively** import the
`AddCommGroup ℤ` instance (in `Mathlib.Algebra.Group.Int.Defs`). The
G6 file references `ℤ →+ G` and `G →+ ℤ` in lines 71, 80, 81, all of
which need `AddZero ℤ` for the synthesizer to find `AddMonoidHom`'s
`Zero` instance.

**Fix**: 1-LOC import addition — `import Mathlib.Algebra.Group.Int.Defs`.

**Build #2 succeeded** in 316 jobs (much smaller than the ~600 jobs
predicted by S12 PREP §5; the G6 file's transitive import closure is
shallower than expected because it does NOT touch category theory).

## 2. Build #1 failure (pre-fix)

```
error: Proofs/BrouwerFixedPointOQ01OQ02G6.lean:71:22: failed to synthesize
  AddZero ℤ
error: Proofs/BrouwerFixedPointOQ01OQ02G6.lean:71:48: unsolved goals
  ...
  φ : sorry
  ψ : sorry
  ⊢ sorry = 0
error: Proofs/BrouwerFixedPointOQ01OQ02G6.lean:80:9: failed to synthesize
  AddZero ℤ
error: Proofs/BrouwerFixedPointOQ01OQ02G6.lean:80:22: failed to synthesize
  AddZero ℤ
error: Proofs/BrouwerFixedPointOQ01OQ02G6.lean:81:15: failed to synthesize
  AddZero ℤ
error: Lean exited with code 1
error: build failed
```

Both `(φ : ℤ →+ G)` and `(ψ : G →+ ℤ)` in `comp_through_subsingleton_is_zero`
(line 71) and `no_split_through_subsingleton` (lines 80–81) require
`AddZero ℤ` for the `→+` arrow's typeclass resolution. With only
`Mathlib.Algebra.Group.Hom.Basic` imported, this instance is missing.

(The `unique_hom_to_subsingleton` and `hom_from_subsingleton_is_zero`
helpers — lines 50–64 — also use `AddMonoidHom` but in generic
`{G H : Type*} [AddCommGroup G] [AddCommGroup H]` form, so they
don't need any ℤ-specific instance. They compiled clean. Only the two
ℤ-referencing theorems failed.)

## 3. The fix

```diff
 import Mathlib.Algebra.Group.Hom.Basic
+import Mathlib.Algebra.Group.Int.Defs

 namespace BrouwerOQ01OQ02
```

`Mathlib.Algebra.Group.Int.Defs` at pin `2df2f015…` provides:

```lean
instance instAddCommGroup : AddCommGroup ℤ where ...   -- line 39
instance instAddCommMonoid : AddCommMonoid ℤ := by infer_instance   -- line 77
instance instAddMonoid : AddMonoid ℤ := by infer_instance           -- line 78
instance instAddGroup : AddGroup ℤ := by infer_instance             -- line 82
```

The `AddCommGroup ℤ` instance (line 39) transitively provides
`AddZero ℤ`, satisfying the synthesizer for both `ℤ →+ G` and `G →+ ℤ`.

## 4. Build #2 success

```
✔ [316/316] Built Proofs.BrouwerFixedPointOQ01OQ02G6 (2.1s)
Build completed successfully (316 jobs).
=== Build succeeded ===
```

**Job count**: 316 (vs ~600 predicted by S12 PREP §5). The shallower
transitive closure reflects G6's minimal import set (algebra only — no
category theory, no topology, no analysis). This is good news for any
future incremental builds touching the G6 file.

**Wall-clock**: ~3.5 min total (cache fetch 28s + decompress 29s +
~120s build).

## 5. Status after this ACT

| File | LOC | Theorems | Axioms | Sorries | Build |
|------|-----|----------|--------|---------|-------|
| `proofs/Proofs/BrouwerFixedPointOQ01OQ02.lean` | 462 | 14 | 4 | 0 | (unchanged) |
| `proofs/Proofs/BrouwerFixedPointOQ01OQ02G6.lean` | **88** | 4 | 0 | 0 | **✅ verified (316 jobs)** |
| `proofs/Proofs/BrouwerFixedPointOQ01OQ02G7.lean` | 94 | 2 | 0 | 0 | (unchanged) |
| `proofs/Proofs/BrouwerFixedPointOQ01OQ02G8.lean` | 134 | 2 | 0 | 0 | (unchanged) |
| **Total** | **778** | **22** | **4** | **0** | **all 4 verified** |

The S9 ACT-D-3 EXEC readiness gate **advances to 8/8 GREEN** (was 7/8 +
AMBER on G6 build-pending). The substantive integration step (S14
ACT-D-3 EXEC per the existing state.md) is now unblocked.

## 6. Bridge taxonomy (4/4 bridges Docker-verified)

| Bridge | On main? | Build-verified |
|--------|----------|----------------|
| **G6** (`id ℤ` cannot factor through subsingleton) | Yes (#19624) | **✅ This ACT (316 jobs)** |
| **G7** | Yes (#18951) | ✅ (S9, 718 jobs) |
| **G8** | Yes (#19114) | ✅ (S9, 627 jobs) |
| **G9** | Yes (#19114) | ✅ (S9, 627 jobs) |

## 7. Anti-targets

- No `state.md` / JSON edit (S14 STATE-SYNC scope reserved; this S13b
  ACT ships only the Lean fix + this session note).
- No `problem.md` / `knowledge.md` body edit.
- No edits to G7, G8, parent G files, or main file.
- No `meta.json` edit (Lean LOC delta is +1; no theorem count change).
- No `lakefile.toml` / `lake-manifest.json` edit.

## 8. Honesty notes

- **Cache-hit-only**: Build #2 hit Mathlib cache for 7727 files. A
  cold-cache build would take significantly longer; this ACT did not
  test cold-cache build.
- **The fix surfaces a documentation gap in S12 PREP §5**. The F1–F4
  risk inventory caught `AddMonoidHom.ext`, `Subsingleton.elim`,
  `map_zero`, `zero_comp` — all internal API risks. It did NOT catch
  the import-completeness risk for the `ℤ`-specific `AddZero` instance,
  even though the file's `ℤ →+ G` / `G →+ ℤ` shapes were known upfront.
  Worth noting in any future PREP risk inventories: **the typeclass
  closure of imported modules is itself a verification target**.
- **No alternative fixes evaluated**. The single-import fix
  (`Mathlib.Algebra.Group.Int.Defs`) is minimal and matches the
  S12 PREP §5 "import-discipline" stance ("no new imports beyond
  Mathlib.Algebra.Group.Hom.Basic and the integer dependencies that
  AddMonoidHom + the integer-Zero instance already pull transitively"
  — except in this case the assumed transitive closure did not hold).
  Alternative: `import Mathlib.Data.Int.Defs` (broader, possibly
  larger build closure). The S13b fix takes the minimal route.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
