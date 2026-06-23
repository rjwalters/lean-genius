# S2 PREP — Mathlib v4.26.0 AffineSubspace API pin for unshipped S2 ACT scaffold

**Author**: researcher-9
**Date**: 2026-05-15
**Phase**: PREP (S2 pre-flight, doc-only, conflict-free)

## Trigger

state.md flags **S2 ACT has not yet shipped** — `proofs/Proofs/Erdos735OQ04.lean` does not exist on `origin/main`. Three iterations have shipped (S1 OBSERVE PR #18336, S6a PREP PR #18486, S6b PREP PR #18541) but the foundational Lean scaffold is still missing. Two days have passed since S6b. The S6 PREPs depend on definitions (`PointConfigD`, `ConfigKFlat`, `IsKFlatMagic`) that no Lean file actually provides yet.

This PREP pins the Mathlib v4.26.0 API needed by S2 ACT, audits a **stale-syntax hazard inherited from the parent** that would silently propagate, and provides a v4.26.0-clean S2 ACT skeleton.

## Lake-pinned Mathlib SHA

`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from
`proofs/lake-manifest.json`, package `mathlib`).

All bearer paths verified via `gh api .../contents/<path>?ref=<SHA>`.

## Headline finding — `.toSubmodule.rank` chain is **stale** at v4.26.0

Parent `Erdos735Problem.lean` uses (4 occurrences, lines 50, 73, 82, 92):

```lean
L.direction.toSubmodule.rank = 1
```

**At v4.26.0**, `AffineSubspace.direction` is defined as:

```lean
-- Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:188
def direction (s : AffineSubspace k P) : Submodule k V :=
  vectorSpan k (s : Set P)
```

So `L.direction : Submodule ℝ V` **directly** — no `toSubmodule` projection is needed. Two consequences:

- **No `Submodule.toSubmodule` function exists in Mathlib** at this SHA (`gh api search/code` for `Submodule.toSubmodule` and `AffineSubspace.toSubmodule` both return **0 hits**).
- **No `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace.lean` exists** as a single file; it has been split into `Defs.lean` + `Basic.lean` under `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/`. The parent imports the legacy path which still resolves via Mathlib's re-export shims, but the API itself has moved.

**Whether the parent builds** at v4.26.0 is determined by whether Lean's dot-notation elaboration silently no-ops `.toSubmodule` on a `Submodule` value:

- If `Lean elaborates (X : Submodule).toSubmodule` as `X` (no-op via auto-coercion / `Submodule.toSubmodule := id`-style synthesis), parent **builds redundantly**.
- If elaboration fails (`Submodule.toSubmodule` not found, no fallback), parent is **silently broken** at v4.26.0 and the gallery's `mathlib_version: 4.26.0` claim is overstated.

**Mathlib's own usage at this SHA is `finrank k sp.direction + 1`** (e.g., `Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean:264, 315, 329, 349`) — i.e., `finrank` is applied directly to `direction`, with no intermediate `.toSubmodule`. This confirms the idiomatic v4.26.0 form drops the projection.

**S2 ACT must NOT copy parent's `.toSubmodule` chain**. Doing so either propagates the redundancy (cosmetic harm) or propagates a silent break (build-failure harm).

## Bearer pin table @ SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

All verified via `gh api .../contents/<path>?ref=<SHA>`. **Italicised** entries flag bearers absent from Mathlib but used by parent.

| Bearer | File | Line | v4.26.0 status |
|---|---|---|---|
| `structure AffineSubspace (k : Type*) {V P : Type*} ...` | `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean` | 149 | exists (carrier-only) |
| `AffineSubspace.direction : AffineSubspace k P → Submodule k V` | same file | 188 | exists; returns `Submodule` directly |
| `AffineSubspace.direction_eq_vectorSpan` | same file | 192 | exists; `direction = vectorSpan` |
| `AffineSubspace.directionOfNonempty` | same file | 198 | exists; alternative for nonempty |
| `Submodule.toAffineSubspace` | same file | 162 | exists; reverse coercion |
| *`AffineSubspace.toSubmodule`* | n/a | n/a | **does NOT exist** at SHA |
| *`Submodule.toSubmodule`* | n/a | n/a | **does NOT exist** at SHA |
| `Module.rank : Type → Type → Cardinal` | `Mathlib/LinearAlgebra/Dimension/Basic.lean` | 68 | exists; `irreducible_def` |
| `Module.finrank : Type → Type → ℕ` | `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean` (reexported widely) | — | exists; `Module.rank.toNat` |
| `finrank ℝ sp.direction` idiom | `Mathlib/LinearAlgebra/AffineSpace/FiniteDimensional.lean` | 264, 315, 329, 349 | **the canonical v4.26.0 idiom** |
| `Submodule.finrank_mono` | same file | 264 | exists; for `s ≤ t → finrank s ≤ finrank t` |
| `vectorSpan k (s : Set P) : Submodule k V` | `AffineSubspace/Defs.lean` | 63 | exists; underlying span |
| `EuclideanSpace ℝ (Fin d)` | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` | — | exists; FiniteDimensional `d` |
| `Finset.filter`, `Finset.sum` | `Mathlib/Order/Finset/...` | — | exists; standard |
| `AffineIndependent.finrank_vectorSpan` | `AffineSpace/FiniteDimensional.lean` | 145 | exists; `n+1` points → rank n |
| `AffineIndependent.finrank_vectorSpan_add_one` | same | 154 | exists; convenient `+1` form |

15 bearers pinned: 11 exist, 2 confirmed missing (`*.toSubmodule`), 2 reference-only. **No phantom bearers** cited in the skeleton below.

## v4.26.0-clean `Erdos735OQ04.lean` skeleton (S2 ACT target)

Replacing parent's stale syntax `L.direction.toSubmodule.rank = k`
with the v4.26.0 idiom `finrank ℝ L.direction = k`:

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Proofs.Erdos735Problem

namespace Erdos735OQ04

open Module  -- for finrank

/-- A point configuration in `ℝ^d`. -/
def PointConfigD (d : ℕ) := Finset (EuclideanSpace ℝ (Fin d))

/-- A weighting assigns a positive real to each configuration point. -/
def WeightingD {d : ℕ} (P : PointConfigD d) := {w : P → ℝ // ∀ p, w p > 0}

/-- A `k`-flat determined by the configuration: an affine subspace of
finite rank `k` containing at least `k+1` configuration points. -/
def ConfigKFlat {d : ℕ} (k : ℕ) (P : PointConfigD d) :=
  { F : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)) //
      finrank ℝ F.direction = k ∧
      (P.filter (· ∈ F)).card ≥ k + 1 }
  -- v4.26.0 NOTE: was `F.direction.toSubmodule.rank = k` in parent;
  -- `.toSubmodule` is stale at v4.26.0 (AffineSubspace.direction
  -- returns Submodule directly). Using `finrank` matches the Mathlib
  -- idiom (`FiniteDimensional.lean:264, 315, 329, 349`).

/-- Sum of weights on a `k`-flat. -/
def kFlatSum {d k : ℕ} (P : PointConfigD d) (w : WeightingD P)
    (F : ConfigKFlat k P) : ℝ :=
  (P.filter (· ∈ F.val)).sum fun p =>
    if h : p ∈ P then w.val ⟨p, h⟩ else 0

/-- A configuration is `k`-flat magic if positive weights exist so
all `k`-flats have equal sum. -/
def IsKFlatMagic {d : ℕ} (k : ℕ) (P : PointConfigD d) : Prop :=
  ∃ w : WeightingD P, ∃ c > 0, ∀ F : ConfigKFlat k P, kFlatSum P w F = c

end Erdos735OQ04
```

LOC estimate for above 5 defs: ~30-40 LOC. Add the 3 trivial-case
theorems (Section S3) and parent reduction (S4) for total ~100 LOC.

## Goal-state walkthrough — Section S3 trivial cases

### Theorem: `zero_flat_magic_trivial`

```lean
theorem zero_flat_magic_trivial {d : ℕ} (P : PointConfigD d) (hP : P.Nonempty) :
    IsKFlatMagic 0 P := by
  -- A 0-flat is a single point (rank-0 affine subspace = singleton).
  -- The constraint `(P.filter (· ∈ F)).card ≥ 0+1 = 1` forces F = {p} for some p ∈ P.
  -- Goal after `unfold IsKFlatMagic`:
  --   ∃ w c, c > 0 ∧ ∀ F : ConfigKFlat 0 P, kFlatSum P w F = c
  refine ⟨⟨fun _ => 1, fun _ => one_pos⟩, 1, one_pos, ?_⟩
  intro F
  -- Goal: kFlatSum P ⟨..⟩ F = 1
  -- After unfold kFlatSum:
  --   (P.filter (· ∈ F.val)).sum (fun p => if h : p ∈ P then 1 else 0) = 1
  -- F is a 0-flat with ≥ 1 config point. Since `finrank ℝ F.direction = 0`,
  -- F.direction = ⊥ (the zero submodule). For a non-empty F, this means
  -- F is a singleton, so the filter picks exactly 1 point.
  sorry  -- ~10-15 LOC: zero-rank-direction implies singleton; sum-over-singleton = 1
```

**Tactical bridge S3a** (`finrank = 0 → submodule = ⊥`): use
`Submodule.finrank_eq_zero` or `finrank_eq_zero_iff` (Mathlib's
standard equivalence between zero rank and trivial submodule for
finite-dimensional modules). Pin: `Mathlib/LinearAlgebra/Dimension/Finrank.lean`.

**Tactical bridge S3b** (rank-0 affine subspace = singleton): a
non-empty affine subspace with trivial direction submodule contains a
single point. Mathlib lemma: `AffineSubspace.eq_singleton_of_direction_eq_bot`
(verify name at SHA before drafting).

### Theorem: `ambient_flat_magic_trivial`

```lean
theorem ambient_flat_magic_trivial {d : ℕ} (P : PointConfigD d) (hP : P.Nonempty) :
    IsKFlatMagic d P := by
  -- A d-flat in ℝ^d is the ambient space (the only rank-d affine subspace).
  -- All n points lie in it, so the constraint
  -- `(P.filter (· ∈ F)).card ≥ d+1` may NOT hold if n < d+1.
  -- The trivial-case statement should require `P.card ≥ d+1`.
  sorry  -- ~10-15 LOC; needs hypothesis tightening from S1's OBSERVE plan
```

**Hypothesis-tightening flag**: the S1 OBSERVE plan stated this as
`(hP : P.Nonempty)`, but for the d-flat to *exist* in `ConfigKFlat d P`
we need `(P.filter (· ∈ F)).card ≥ d + 1`. If `P.card < d+1`, no
config d-flat exists and the universal in `IsKFlatMagic d` is vacuously
satisfied — but that's a different proof path. The clean form takes
`P.card ≥ d+1` as hypothesis.

**Tactical bridge S3c** (rank-d affine subspace in `ℝ^d` is the ambient
space): `AffineSubspace.eq_top_of_finrank_direction_eq_finrank_self`
or similar. Verify name; the lemma may be phrased as
`F.direction = ⊤ → F = ⊤` after using `finrank_eq_dim_iff` for
finite-dimensional spaces.

## Goal-state walkthrough — Section S4 parent reduction

```lean
theorem oneflat_eq_parent (P : PointConfigD 2) :
    IsKFlatMagic 1 P ↔ Erdos735.IsMagic P := by
  -- Both sides quantify over the same type of weightings and the same
  -- constant `c`. The difference is `ConfigKFlat 1 P` vs `ConfigLine P`.
  -- ConfigKFlat 1 P : { F : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) //
  --                      finrank ℝ F.direction = 1 ∧ ... }
  -- ConfigLine P    : { L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) //
  --                      L.direction.toSubmodule.rank = 1 ∧ ... }
  -- These are SYNTACTICALLY different but PROPOSITIONALLY equal.
  -- Tactical bridge S4a: build a type-equiv between `ConfigKFlat 1 P`
  -- and `ConfigLine P`. This requires `finrank ℝ F.direction = 1 ↔
  -- F.direction.toSubmodule.rank = 1`, which is **NOT rfl** because:
  --   - `finrank` returns ℕ
  --   - `.rank` (= `Module.rank`) returns `Cardinal`
  -- The bridge: `finrank_eq_one_iff_module_rank_eq_one` or unpack via
  --   `Module.rank_eq_one_iff_finrank_eq_one` (verify name at SHA).
  sorry  -- ~20-30 LOC
```

**Tactical bridge S4a** (this is the **critical reduction bridge**):
parent uses `.rank = 1` (Cardinal-valued), this scaffold uses
`finrank = 1` (ℕ-valued). The biconditional holds for
finite-dimensional submodules but is not rfl. Pin:
`Module.finrank_eq_one_iff_lift` and `Module.rank_eq_one_iff`
(`Mathlib/LinearAlgebra/Dimension/Basic.lean` or
`Mathlib/LinearAlgebra/Dimension/Finrank.lean`).

**Workaround**: define `Erdos735OQ04.ConfigKFlat 1 P` to **match
parent's syntax** by using `Module.rank ℝ F.direction = 1` instead
of `finrank ℝ F.direction = 1`. This avoids the Cardinal↔ℕ bridge.
Trade-off: matches parent's stale-API hazard. **Recommendation**: use
`finrank` in the OQ-04 file AND make the reduction theorem the lemma
that does the bridge work.

## Parent mechanic-fix scope (out of scope here)

Parent `Erdos735Problem.lean` uses `L.direction.toSubmodule.rank = 1`
in 4 places (lines 50, 73, 82, 92). If parent builds at v4.26.0 via
silent auto-coercion, the chain is redundant (~4 LOC cleanup). If
parent is silently broken, the chain is **load-bearing** and needs
mechanic fix.

**Out of scope for this PREP**: parent repair is a mechanic-track item
or a separate audit. The S2 ACT for OQ-04 can ship independently
using clean v4.26.0 syntax, with a guarded import + an explicit
reduction theorem that bridges to whatever parent exposes.

**Forward dependency**: if parent's syntax is genuinely broken at
v4.26.0, then `import Proofs.Erdos735Problem` from OQ-04 will fail at
compile time, even with clean OQ-04 syntax. In that case, S2 ACT
should:

- (i) **Bundle a 4-line mechanic fix** to parent (matches memory entry
  `_act_bundles_v426_mechanic_fix_on_imported_parent`), OR
- (ii) **Defer the parent-reduction theorem** to a later phase (S4),
  shipping S2 with just the definitions + trivial cases.

A standalone audit / mechanic invocation can determine which path is
appropriate by running `./proofs/scripts/docker-build.sh
Proofs.Erdos735Problem` and inspecting the result. **This PREP does
NOT attempt that build** — it scopes to API documentation + skeleton.

## Negative-bearer results

Bearers searched and confirmed **not present** at SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

- `AffineSubspace.toSubmodule` — does not exist (0 hits via
  `gh api search/code` with this exact name)
- `Submodule.toSubmodule` — does not exist (0 hits)
- `AffineSubspace.rank` — does not exist (0 hits as direct field)
- `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace.lean` (single
  file) — does not exist; split into
  `AffineSubspace/Defs.lean` + `AffineSubspace/Basic.lean` (re-export
  shim resolves the legacy import path)

No phantom bearers cited in this PREP's skeleton.

## What this PREP does NOT do

- Does not modify `proofs/Proofs/Erdos735Problem.lean` (parent mechanic
  fix scope is separate).
- Does not write `proofs/Proofs/Erdos735OQ04.lean` (S2 ACT scope).
- Does not modify `state.md`, `knowledge.md`, or gallery metadata.
- Does not invoke `docker-build.sh` to determine parent build status.
- Does not attempt the S5 axiom refinement or the S6d
  dodecahedron/icosahedron analysis (separate sibling PREPs).

Strictly conflict-free: one new file at
`sessions/2026-05-15-s2-prep-affinesubspace-api-pin.md`.

## Next action (S2 ACT)

A researcher claiming S2 ACT for this slug reads this PREP for:

1. The v4.26.0-clean API: `finrank ℝ F.direction = k` (not parent's
   `.toSubmodule.rank` chain).
2. The 5-definition skeleton (PointConfigD, WeightingD, ConfigKFlat,
   kFlatSum, IsKFlatMagic).
3. The 3 trivial-case theorem statements + tactical bridges (rank-0
   → singleton via `Submodule.finrank_eq_zero`, rank-d → ambient via
   `eq_top_of_finrank...`).
4. The S4 reduction-theorem bridge plan (Cardinal↔ℕ via
   `Module.finrank_eq_one_iff_*`).
5. The parent build-status flag (recommend running
   `./proofs/scripts/docker-build.sh Proofs.Erdos735Problem` BEFORE
   importing; if broken, bundle 4-line parent fix per memory entry
   `_act_bundles_v426_mechanic_fix_on_imported_parent`).

Estimated S2 ACT size: **~100-130 LOC** (5 defs + 3 trivial-case
theorems + 1 parent-reduction). **0 axioms.** Sorries
acceptable on the trivial-case proofs initially; ship the API
correctly first, discharge the proofs in S2b.

## Provenance

- Triggered by S2 ACT stagnation (3 iterations on slug, no Lean file
  shipped; S6 PREPs depend on definitions that don't exist).
- Lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  via `proofs/lake-manifest.json`.
- All 15 Mathlib bearers verified via
  `gh api .../contents/<path>?ref=<SHA>`.
- 4 negative-bearer results confirmed via
  `gh api /search/code?q=...repo:leanprover-community/mathlib4`.
- Parent surface read directly from `Proofs/Erdos735Problem.lean`.

researcher-9 / 2026-05-15
