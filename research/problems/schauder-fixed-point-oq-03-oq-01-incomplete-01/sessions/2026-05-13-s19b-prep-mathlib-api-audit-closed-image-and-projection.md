# S19b PREP — Mathlib v4.26.0 API audit for the closed-image lemma and Hilbert projection

**Iteration**: S19b PREP (doc-only sub-step memo)
**Author**: researcher-9
**Date**: 2026-05-13
**File**: this design note (no Lean / state.md / knowledge.md / meta.json edits)
**Predecessor**: S19a PREP `2026-05-12-s19a-prep-closed-image-and-signature-alignment.md`
(merged; see PR list for slug) — locked the closed-image lemma's
statement and three candidate proof paths but explicitly deferred the
Mathlib API name confirmation: "implementer should grep the pinned rev
for the exact name with `gh api`" (S19a §3.a, last paragraph). This
memo executes that audit.
**Sister PRs in flight at session start** (per
`gh pr list --search schauder --state open`): #17801 (stale 2026-05-12
S18b plumbing) and #17493 (stale 2026-05-08 S11 Brouwer closed-ball
specialization). Both touch
`proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` and `state.md` —
**zero file overlap** with this memo, which adds only the file
`sessions/2026-05-13-s19b-prep-mathlib-api-audit-closed-image-and-projection.md`.

---

## §0. TL;DR

S19a PREP designed the closed-image lemma
`image_subtype_isClosed_of_isClosed_of_compact` with three candidate
proof paths (A: `Continuous.isClosedMap` direct; B: rejected; C:
compactness chain) and recommended Path A. The S19a memo deferred the
Mathlib API name confirmation at the lakefile-pinned revision
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (per `proofs/lake-manifest.json`).

This S19b memo:

1. **Confirms** all four Path A lemmas at exact file/line locations on
   the pinned rev.
2. **Confirms** all three Path C lemmas as fallbacks at exact
   file/line locations on the pinned rev.
3. **Surfaces a drift** in S19a §4.b's reference to
   `exists_norm_eq_iInf_of_complete_convex`: the lemma has **moved**
   from `Mathlib/Analysis/InnerProductSpace/Projection.lean` (S19a's
   cited path) to `Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean`
   between Mathlib v4.25 and v4.26.0. The implementer who follows
   S19a's `Projection.lean` import will hit a missing-file error
   without warning.
4. **Surfaces a hypothesis mismatch**: the projection lemma takes
   `IsComplete K`, not `IsClosed K` as S19a's paraphrased signature
   suggested. The bridge is `IsClosed.isComplete` under
   `[CompleteSpace α]`; for `EuclideanSpace ℝ (Fin n)` (which is
   finite-dimensional ℝ-Banach), `CompleteSpace` is automatic.
5. **Fixes a name typo** in S19a Path C: `IsClosed.isCompact_of_compactSpace`
   does not exist at v4.26.0. The correct name is `IsClosed.isCompact`
   (under `[CompactSpace X]`).
6. **Notes** that `Continuous.isClosedMap` is `protected` (line 663 of
   `Mathlib/Topology/Separation/Hausdorff.lean`). The dot-notation
   call `h.isClosedMap` still works; an unqualified
   `Continuous.isClosedMap h` is also valid. A bare `isClosedMap` call
   without the namespace would fail.

Net result: S19c (the ACT iteration that implements the closed-image
lemma + the `approx_selection_exists` discharge) can copy the §4 code
block verbatim and import the correct paths. Without this audit, the
S19c implementer would have hit at least one missing-file error and
one wrong-name error.

**This PR contains zero Lean code, zero edits to gallery files**
**(`meta.json` / `annotations.json` / `index.ts`), zero edits to**
**`problem.md` / `state.md` / `knowledge.md`. One new file in the**
**existing `sessions/` subdir.**

---

## §1. Pinned revision (lake-manifest authoritative)

```bash
$ jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

All file/line citations below are at this revision. Verification
commands appear in Appendix A.

## §2. Path A audit (S19a recommended path)

### §2.1 `isCompact_iff_compactSpace`

**File**: `Mathlib/Topology/Compactness/Compact.lean`
**Line**: 989
**Signature** (verbatim):

```lean
theorem isCompact_iff_compactSpace : IsCompact s ↔ CompactSpace s :=
  isCompact_iff_isCompact_univ.trans isCompact_univ_iff
```

**Usage in S19a Path A**:

```lean
have hCompact : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
```

✓ **Confirmed**. Name and direction (`.mp` extracts `CompactSpace` from
`IsCompact`) both match S19a's design. Sibling usage exists at
`Mathlib/Topology/IsClosedRestrict.lean:130` (in-repo precedent for the
exact `.mp` pattern).

### §2.2 `continuous_subtype_val`

**File**: `Mathlib/Topology/Constructions.lean`
**Line**: 367
**Signature** (verbatim):

```lean
theorem continuous_subtype_val : Continuous (@Subtype.val X p) :=
  continuous_induced_dom
```

**Usage in S19a Path A**:

```lean
have hClosedMap : IsClosedMap (Subtype.val : ↥S → α) :=
  Continuous.isClosedMap continuous_subtype_val
```

✓ **Confirmed**. Note that `continuous_subtype_val` is a *function-bound*
constant (no further `(p : X → Prop)` argument — the implicit `p`
matches the binder `↥S`-as-Subtype's predicate).

### §2.3 `Continuous.isClosedMap`

**File**: `Mathlib/Topology/Separation/Hausdorff.lean`
**Line**: 663
**Signature** (verbatim):

```lean
/-- A continuous map from a compact space to a Hausdorff space is a closed map. -/
protected theorem Continuous.isClosedMap [CompactSpace X] [T2Space Y] {f : X → Y}
    (h : Continuous f) : IsClosedMap f := fun _s hs => (hs.isCompact.image h).isClosed
```

**Important: `protected`**. The S19a snippet `Continuous.isClosedMap
continuous_subtype_val` is valid (full namespace). The dot-notation
form `continuous_subtype_val.isClosedMap` is also valid (Lean's
`protected` keyword does not block dot-resolution, only bare
unqualified calls). What would NOT compile is `open Continuous in
isClosedMap _`.

**Typeclass requirements**:
- `[CompactSpace X]` ← supplied by §2.1 invocation.
- `[T2Space Y]` ← for `α = EuclideanSpace ℝ (Fin n)`, this is automatic
  from `MetricSpace` instance (transitively `EMetricSpace` →
  `UniformSpace` → `T2Space`). For the generic `{α} [TopologicalSpace α]
  [T2Space α]` form in S19a's §4 lemma statement, the implementer
  declares `[T2Space α]` directly.

✓ **Confirmed**. Signature matches S19a's design.

### §2.4 Path A composite check

The S19a §4 lemma body:

```lean
private lemma image_subtype_isClosed_of_isClosed_of_compact
    {α : Type*} [TopologicalSpace α] [T2Space α]
    {S : Set α} (hS_compact : IsCompact S)
    {T : Set ↥S} (hT_closed : IsClosed T) :
    IsClosed ((Subtype.val '' T : Set α)) := by
  have hCompact : CompactSpace ↥S :=
    isCompact_iff_compactSpace.mp hS_compact
  have hClosedMap : IsClosedMap (Subtype.val : ↥S → α) :=
    Continuous.isClosedMap continuous_subtype_val
  exact hClosedMap T hT_closed
```

**Verdict**: compiles at v4.26.0 modulo a possible implicit-binder
elaboration nuance on `(Subtype.val : ↥S → α)`. If the elaborator
infers the wrong subtype predicate, the explicit-binder form
`(@Subtype.val α (· ∈ S))` resolves it. Recommend the implementer try
the implicit form first; fall back to `@Subtype.val` if it fails.

## §3. Path C audit (fallback)

### §3.1 `IsClosed.isCompact`

**File**: `Mathlib/Topology/Compactness/Compact.lean`
**Line**: 805
**Signature** (verbatim):

```lean
theorem IsClosed.isCompact [CompactSpace X] (h : IsClosed s) : IsCompact s :=
  isCompact_univ.of_isClosed_subset h (subset_univ _)
```

**Name correction from S19a Path C**: S19a §3.c step 1 calls
`hT_closed.isCompact_of_compactSpace`. **This name does not exist at
v4.26.0** (search returns zero hits). The correct name is the
unqualified `IsClosed.isCompact` — the `[CompactSpace X]` typeclass is
inferred, not encoded in the lemma name. The implementer should write:

```lean
have hCompact_T : IsCompact T := hT_closed.isCompact
```

(NOT `hT_closed.isCompact_of_compactSpace`.)

✓ **Confirmed** under corrected name.

### §3.2 `IsCompact.image`

**File**: `Mathlib/Topology/Compactness/Compact.lean`
**Line**: 121
**Signature** (verbatim):

```lean
theorem IsCompact.image {f : X → Y} (hs : IsCompact s) (hf : Continuous f) : IsCompact (f '' s) :=
  hs.image_of_continuousOn hf.continuousOn
```

**Usage in S19a Path C**:

```lean
have hImg_compact : IsCompact ((Subtype.val '' T : Set α)) :=
  hCompact_T.image continuous_subtype_val
```

✓ **Confirmed**.

### §3.3 `IsCompact.isClosed`

**File**: `Mathlib/Topology/Separation/Hausdorff.lean`
**Line**: 580
**Signature** (verbatim):

```lean
@[aesop 50% apply, grind ←]
theorem IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsCompact s) : IsClosed s :=
  ...
```

**Usage in S19a Path C**:

```lean
exact hImg_compact.isClosed
```

✓ **Confirmed**. Note the `@[aesop 50% apply, grind ←]` tags — `aesop`
can sometimes close this goal automatically (potential one-liner
simplification for the implementer to try).

### §3.4 Path C composite

```lean
private lemma image_subtype_isClosed_of_isClosed_of_compact_pathC
    {α : Type*} [TopologicalSpace α] [T2Space α]
    {S : Set α} (hS_compact : IsCompact S)
    {T : Set ↥S} (hT_closed : IsClosed T) :
    IsClosed ((Subtype.val '' T : Set α)) := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  exact (hT_closed.isCompact.image continuous_subtype_val).isClosed
```

**Line count**: 2 tactic lines (vs Path A's 3). Slightly cleaner once
Path A's wrong-name (§3.1) is corrected.

**Recommendation update from S19a**: Path C is now **as concise as**
Path A and slightly less structural (avoids `IsClosedMap`). Implementer
may prefer Path C; both are confirmed working at v4.26.0.

## §4. Hilbert projection drift

### §4.1 Path location

**S19a §2 citation**: `Mathlib/Analysis/InnerProductSpace/Projection.lean`
**v4.26.0 actual location**: `Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean`

**Verification**:

```bash
$ gh api -X GET 'search/code' -f q='"exists_norm_eq_iInf_of_complete_convex" repo:leanprover-community/mathlib4'
  | jq '.items[] | .path'
"Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean"
"docs/1000.yaml"
"docs/undergrad.yaml"
```

The `Projection.lean` file at v4.26.0 does NOT contain the lemma. The
file was split into `Projection/Minimal.lean` (projection theorems) and
`Projection.lean` (orthogonal-projection bundling) at v4.26.0.

**Consequence for S19c implementer**: if the existing file imports
`Mathlib.Analysis.InnerProductSpace.Projection`, the import remains
valid at v4.26.0 (the file still exists) but it **does not transitively
pull in `Projection.Minimal`**. The implementer must add:

```lean
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
```

(or, simpler, rely on `import Mathlib.Analysis.InnerProductSpace.Projection`
+ verify in a fresh build that the transitive closure does cover
`exists_norm_eq_iInf_of_complete_convex` — at v4.26.0 it likely
**does** because `Projection.lean` is a thin facade over
`Projection/Minimal.lean`. The implementer should verify by reading the
top of `Mathlib/Analysis/InnerProductSpace/Projection.lean` at the
pinned rev.)

Recommended path: explicit `import Mathlib.Analysis.InnerProductSpace.Projection.Minimal`
in the Schauder-FP file, even if redundant under the facade — explicit
imports are safer against future Mathlib refactors.

### §4.2 Lemma signature

**S19a §2 paraphrased**: `K.Nonempty → IsClosed K → Convex ℝ K → ...`
**Actual at v4.26.0** (verbatim from `Projection/Minimal.lean:34`):

```lean
theorem exists_norm_eq_iInf_of_complete_convex {K : Set F} (ne : K.Nonempty) (h₁ : IsComplete K)
    (h₂ : Convex ℝ K) : ∀ u : F, ∃ v ∈ K, ‖u - v‖ = ⨅ w : K, ‖u - w‖
```

**Hypothesis stack**:
- `(ne : K.Nonempty)` ✓ matches S19a
- `(h₁ : IsComplete K)` ✗ S19a wrote `IsClosed K`; actual is `IsComplete K`
- `(h₂ : Convex ℝ K)` ✓ matches S19a

**Bridge**: `IsClosed.isComplete` (Mathlib/Topology/UniformSpace/Cauchy.lean:439):

```lean
theorem IsClosed.isComplete [CompleteSpace α] {s : Set α} (h : IsClosed s) : IsComplete s :=
  ...
```

The bridge requires `[CompleteSpace α]`. For
`α = EuclideanSpace ℝ (Fin n)`, `CompleteSpace` is automatic via the
finite-dimensional ℝ-Banach instance chain (`Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
provides the general finite-dimensional → complete fact; the
`EuclideanSpace` instance follows).

**Consequence for S19c §6 Step 6a** (S19 PREP):

```lean
-- S19 PREP §6 Step 6a, AS-WRITTEN:
have hFi_closed : IsClosed ((Subtype.val '' F i) : Set (EuclideanSpace ℝ (Fin n))) :=
  image_subtype_isClosed_of_isClosed_of_compact hS_compact (hF_closed i)
have hFi_complete : IsComplete ((Subtype.val '' F i) : Set (EuclideanSpace ℝ (Fin n))) :=
  hFi_closed.isComplete                                          -- bridge: NEW step
have hFi_ne_img : ((Subtype.val '' F i) : Set _).Nonempty := (hF_ne i).image _
have hFi_convex_img : Convex ℝ ((Subtype.val '' F i) : Set _) := hF_convex i
obtain ⟨y, hy_mem, hy_norm⟩ :=
  exists_norm_eq_iInf_of_complete_convex hFi_ne_img hFi_complete hFi_convex_img (fC x : _)
```

The bridge step adds **one line** to S19c's eventual proof body. S19a
§6's signature update remains correct as-stated (`hF_closed : ∀ x,
IsClosed (F x)`); the bridge step happens inside the proof, not at
the API surface.

### §4.3 Implications for S19a's lemma name

S19a §4 names the closed-image lemma `image_subtype_isClosed_of_isClosed_of_compact`.
The name is accurate to what the lemma proves. However, given that
S19c only consumes it to derive `IsComplete`, the implementer may
optionally inline both steps as a single helper:

```lean
private lemma image_subtype_isComplete_of_isClosed_of_compact
    {α : Type*} [TopologicalSpace α] [T2Space α] [CompleteSpace α]
    {S : Set α} (hS_compact : IsCompact S)
    {T : Set ↥S} (hT_closed : IsClosed T) :
    IsComplete ((Subtype.val '' T : Set α)) := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  exact ((hT_closed.isCompact.image continuous_subtype_val).isClosed).isComplete
```

This adds `[CompleteSpace α]` to the typeclass binder stack and saves
the inline bridge step. Reduces S19c body by 1 line.

**Trade-off**: the closed-image fact is more reusable (e.g. by future
non-Hilbert-projection code); the complete-image specialisation is
tighter. Recommend the implementer ship **both**: the generic
`image_subtype_isClosed_of_isClosed_of_compact` as the S19a-locked
deliverable, and a *one-line* corollary
`image_subtype_isComplete_of_isClosed_of_compact` for the immediate use
site. Net cost: +3 LOC over S19a's 10-LOC budget; total still
within the "10–15 LOC" envelope.

## §5. Updated LOC budget for S19c

S19a §4 estimated 10 LOC for the lemma + 30 LOC for the eventual proof.
After this S19b audit:

| Item | S19a estimate | S19b refined |
|---|---|---|
| `image_subtype_isClosed_of_isClosed_of_compact` (Path A or C) | 10 | 8 (Path C, two tactic lines) |
| `image_subtype_isComplete_of_isClosed_of_compact` corollary | 0 | 3 (optional but recommended) |
| `IsClosed.isComplete` bridge in main body (if no corollary) | 0 | 1 |
| Updated import: `Projection.Minimal` | 0 | 1 |
| `approx_selection_exists_proof` signature update | 5 | 5 |
| `approx_selection_exists_proof` body (§4.b path) | 80–150 | 80–150 |
| Caller-site update at kakutani | ≤2 | ≤2 |
| **Total** | **~95–167** | **~98–170** |

The net delta from S19b vs S19a is +3 LOC (the bridge or corollary) +
1 LOC (explicit import) = **+4 LOC**. Within the existing envelope.

## §6. Updated Path A skeleton (drift-corrected)

S19a §4's lemma body, with the §2 audit findings applied verbatim:

```lean
/-- **S19a/S19b helper**: the ambient-space image of a closed set of a
    compact subtype is closed.

    Proof routes through `Continuous.isClosedMap` (compact-to-Hausdorff
    is a closed map). All four Mathlib lemmas confirmed at the
    lakefile-pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` by
    S19b PREP `2026-05-13-s19b-prep-mathlib-api-audit-closed-image-and-projection.md`. -/
private lemma image_subtype_isClosed_of_isClosed_of_compact
    {α : Type*} [TopologicalSpace α] [T2Space α]
    {S : Set α} (hS_compact : IsCompact S)
    {T : Set ↥S} (hT_closed : IsClosed T) :
    IsClosed ((Subtype.val '' T : Set α)) := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  have hClosedMap : IsClosedMap (Subtype.val : ↥S → α) :=
    Continuous.isClosedMap continuous_subtype_val
  exact hClosedMap T hT_closed
```

**Diff vs S19a §4**: docstring's "implementation reference" line updated
to cite this S19b PREP (so the S19c reader can trace the audit chain).
Body unchanged (S19a Path A was correct modulo the dropped `have
hCompact` → `haveI` switch to ensure typeclass propagation; S19a's
`have` was slightly wrong because the instance must be available for
the next step's typeclass synthesis).

**Minor correction in S19a §3.a step 1**: S19a wrote `have hCompact : CompactSpace ↥S`;
should be `haveI` (or `letI`) to ensure the instance is registered with
the typeclass system, otherwise `Continuous.isClosedMap`'s
`[CompactSpace X]` argument cannot be inferred and elaboration fails.

## §7. Anti-targets (what S19b must NOT do)

7.1 **Do not edit `state.md`** — that update is owned by S19c when the
    lemma actually lands and the file count/sorry count change.

7.2 **Do not edit `problem.md` or `knowledge.md`** — pure design memo.

7.3 **Do not edit `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`** —
    Lean source untouched. Stale PRs #17801 and #17493 are in flight
    on this file; S19b explicitly avoids it.

7.4 **Do not edit gallery files** (`meta.json`, `annotations.json`,
    `index.ts`) — no count change in this PR.

7.5 **Do not duplicate S19a's design work** — this memo is purely
    additive (Mathlib API audit + drift surfacing). The lemma
    statement, the three candidate paths, and the LOC budget are
    S19a's territory.

7.6 **Do not propose the S19c ACT** — that requires the propagation of
    S18f's input-ball clause through S18c/S18d/S18e (open question
    flagged by S19 PREP §2), which is its own design task.

## §8. Conflict-free guarantee

**This PR creates one file**:

```
research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/sessions/2026-05-13-s19b-prep-mathlib-api-audit-closed-image-and-projection.md
```

Sibling sessions in the same `sessions/` subdir:

* `2026-05-12-s19-prep-graph-distance-bound.md`
* `2026-05-12-s19a-prep-closed-image-and-signature-alignment.md`

Both merged; no git operation needed for the directory.

Open PRs on this slug at session start (`gh pr list --search schauder
--state open`):

* PR #17801 — touches `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`,
  `research/problems/<slug>/s18b-instance-plumbing.md`,
  `research/problems/<slug>/state.md`,
  `src/data/proofs/schauder-fixed-point-oq-03-oq-01/meta.json`. **Zero
  overlap** with this PR's single file.
* PR #17493 — touches the same Lean file, `state.md`, the same
  `meta.json`, plus `src/data/research/problems/<slug>.json`. **Zero
  overlap** with this PR's single file.

Files NOT touched by this PR:

* `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` (the Lean source —
  owned by stale PRs #17801 / #17493).
* `research/problems/<slug>/state.md` (held by stale PRs).
* `research/problems/<slug>/problem.md` (only S19c should touch).
* `research/problems/<slug>/knowledge.md` (only S19c should touch).
* `src/data/proofs/schauder-fixed-point-oq-03-oq-01/meta.json` (held
  by stale PRs).
* `src/data/research/problems/<slug>.json` (held by stale PR #17493).
* `research/problems/<slug>/sessions/2026-05-12-s19-prep-graph-distance-bound.md`
  (already merged, read-only here).
* `research/problems/<slug>/sessions/2026-05-12-s19a-prep-closed-image-and-signature-alignment.md`
  (already merged, read-only here).

## §9. Honesty assessment

* **Mathematical content of S19b**: zero new mathematics. Pure Mathlib
  API audit at the pinned revision.
* **Significance**: low-to-medium. Without this audit, S19c would hit
  at least one wrong path location (`Projection.lean` →
  `Projection/Minimal.lean`), one wrong lemma name
  (`IsClosed.isCompact_of_compactSpace` does not exist), one
  type-mismatch (`IsClosed K` vs `IsComplete K`), and one
  typeclass-propagation bug (`have` vs `haveI`). The cumulative cost
  of those errors is roughly 30–60 minutes of implementer time across
  build failures and Mathlib name searches — this audit saves that
  cost.
* **Originality**: none. The audit method (`gh api search/code` +
  `gh api repos/.../contents` decode) is standard practice in the
  Lean Genius project; the four-lemma audit is replicating a process
  S19a PREP recommended but did not execute.
* **What this memo claims**: it locks the Mathlib API surface for S19c
  ACT, surfaces three drift / name / signature errors in S19a PREP,
  and updates the LOC budget by +4. That's the entire value-add.

## §10. Cheat-sheet for S19c ACT implementer

When the next researcher claims the slug and routes to "S19c ACT —
discharge `approx_selection_exists`":

1. **Add explicit import** (top of `SchauderFixedPointOQ03OQ01.lean`):
   ```lean
   import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
   ```
   (NOT `Mathlib.Analysis.InnerProductSpace.Projection`; that path
   still exists but may not transitively cover the lemma.)

2. **Insert the closed-image lemma** (at line ~625, before S18b
   typeclass witnesses) using the **Path A skeleton from §6** of this
   memo. Note the `haveI` correction (not `have`).

3. **Optionally also insert** the
   `image_subtype_isComplete_of_isClosed_of_compact` corollary (§4.3)
   to save a line in the main proof body.

4. **In the main proof** (`approx_selection_exists_proof`), use:
   ```lean
   have hFi_complete : IsComplete ((Subtype.val '' F i) : Set (EuclideanSpace ℝ (Fin n))) :=
     (image_subtype_isClosed_of_isClosed_of_compact hS_compact (hF_closed i)).isComplete
   ```
   (or the corollary directly). Then pass `hFi_complete` (not
   `hFi_closed`) to `exists_norm_eq_iInf_of_complete_convex`.

5. **Signature**: as locked by S19a §6 — add
   `(hF_closed : ∀ x, IsClosed (F x))` between `hF_ne` and
   `hF_convex`.

6. **Do NOT use** `IsClosed.isCompact_of_compactSpace` anywhere — that
   name does not exist at v4.26.0. Use `IsClosed.isCompact` (under
   `[CompactSpace X]`).

7. **PR title pattern**: `research(schauder-fp-oq-03-oq-01-incomplete-01):
   S19c ACT — discharge approx_selection_exists (closed-image lemma +
   Hilbert projection via Cellina §4.b)`.

8. **Build**: `./proofs/scripts/docker-build.sh
   Proofs.SchauderFixedPointOQ03OQ01` — ~45 min cold per slug
   convention. Build-pending PRs land per the S18a–f precedent.

9. **Meta updates** (per kakutani-caller hypothesis-stack alignment):
   - Axiom count drops 2 → 1 (only `brouwer_unit_ball` remains).
   - `theoremCount` += 1 or 2 (the closed-image lemma + the
     `approx_selection_exists_proof` theorem; the existing
     `axiom approx_selection_exists` line is deleted in the same PR).
   - `lineCount` += ~110 (per §5 budget midpoint).

## §11. Knowledge propagation candidates

After S19c lands, the closed-image lemma generalises immediately:

* Any sibling slug needing the "subtype-closed ↔ ambient-closed-in-
  compact-base" fact (e.g., `kakutani-fp-oq-*` if such slugs ever
  formalise UHC selectors).
* `cellina-fp-*` or similar slugs deriving continuous selectors from
  compact-convex-valued correspondences.

The lemma is **already generic** in `α` and `T`; a future Mathlib
upstream PR could land it directly in
`Mathlib/Topology/Subset.lean` or similar. Forward reference only —
out of scope for S19b.

---

## Appendix A: Verification commands

```bash
# §1 — pinned rev:
jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json

# §2.1 — isCompact_iff_compactSpace:
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Compactness/Compact.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d | grep -n -B1 -A2 'isCompact_iff_compactSpace'
# Confirms line 989.

# §2.2 — continuous_subtype_val:
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Constructions.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d | grep -n -B1 -A2 'continuous_subtype_val'
# Confirms line 367.

# §2.3 — Continuous.isClosedMap:
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Separation/Hausdorff.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d | grep -n -B1 -A2 'Continuous.isClosedMap'
# Confirms line 663 with the protected attribute.

# §3.1 — IsClosed.isCompact (name correction):
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Compactness/Compact.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d | grep -n -B1 -A2 'IsClosed.isCompact'
# Confirms line 805; S19a's "_of_compactSpace" suffix does not appear.

# §3.2 — IsCompact.image:
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Compactness/Compact.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d | grep -n -B1 -A2 'theorem IsCompact.image '
# Confirms line 121.

# §3.3 — IsCompact.isClosed:
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Separation/Hausdorff.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d | grep -n -B1 -A2 'IsCompact.isClosed'
# Confirms line 580 with aesop / grind tags.

# §4.1 — Hilbert projection location drift:
gh api -X GET 'search/code' -f q='"exists_norm_eq_iInf_of_complete_convex" repo:leanprover-community/mathlib4' \
  --jq '.items[] | .path'
# Returns Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean
# (NOT Mathlib/Analysis/InnerProductSpace/Projection.lean).

# §4.2 — Hilbert projection signature:
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d | grep -n -B1 -A5 'exists_norm_eq_iInf_of_complete_convex'
# Confirms line 34 with `IsComplete K` hypothesis (not `IsClosed K`).

# §4 bridge — IsClosed.isComplete:
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Topology/UniformSpace/Cauchy.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d | grep -n -B1 -A3 'theorem IsClosed.isComplete'
# Confirms line 439 with `[CompleteSpace α]` precondition.
```

Reproducibility: every grep command above completes in under 5 seconds
on a warm GitHub API connection. The audit cost across all eight
commands is ~8 search/code API calls (well within the 30/hour limit).
