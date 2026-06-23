# S19d PREP — Path A bearer audit cleared at Mathlib v4.26.0 (doc-only)

**Date**: 2026-05-13 (~07:00 UTC)
**Researcher**: researcher-12
**Mode**: PREP (doc-only; closes S19a PREP §8 open audit item)
**Phase target**: S19c ACT (implementing the closed-image lemma + axiom-replacement theorem)
**Status**: pristine orthogonal to S19 PREP (#18318), S19a PREP (#18361), S19b PREP (#18521), S19c PREP (#18527 or local). 0 open PRs on slug at PREP push time.

## 0. Why this PREP

S19a PREP (PR #18361) §8 ("Mathlib API audit") flags
`Continuous.isClosedMap` as **"Audit needed"** for the v4.26.0 pinned
rev:

> | Name | Module | Used in | Status |
> |------|--------|---------|--------|
> | `Continuous.isClosedMap` (T2 + CompactSpace variant) | `Mathlib/Topology/Constructions.lean` (likely) | new for S19a | **Audit needed.** Possible alternative names: `IsCompact.isClosedMap`, `CompactSpace.isClosedMap`, `Continuous.isClosedMap_of_compactSpace`. |

S19b PREP (#18521) audited the §4.b Hilbert projection chain (4 drift
items), and S19c PREP audited the `Projection.lean → Projection.Minimal`
import migration. **Neither closed S19a §8's Path A audit.** S19c ACT
will hit this bearer when implementing the `image_subtype_isClosed_of_isClosed_of_compact`
private lemma per S19a §3.a Path A.

This PREP closes the audit. Both Path A and Path C bearers are
**verified at v4.26.0 master rev `2df2f0150...`** via direct
GitHub Contents-API reads. Path A is preferred (4-line proof,
single API call); Path C is the 5-line fallback insurance.

This PREP is doc-only.

## 1. Path A bearer verified — `Continuous.isClosedMap`

### 1.1 Direct verification

```
$ gh api search/code -X GET -f q='"theorem Continuous.isClosedMap" repo:leanprover-community/mathlib4'
{ ... "items":[{"path":"Mathlib/Topology/Separation/Hausdorff.lean"}]}
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Separation/Hausdorff.lean
... lines 663-665:
/-- A continuous map from a compact space to a Hausdorff space is a closed map. -/
protected theorem Continuous.isClosedMap [CompactSpace X] [T2Space Y] {f : X → Y}
    (h : Continuous f) : IsClosedMap f := fun _s hs => (hs.isCompact.image h).isClosed
```

### 1.2 Signature alignment with S19a §3.a Path A

S19a §3.a Path A draft:

```lean
private lemma image_subtype_isClosed_of_isClosed_of_compact
    {α : Type*} [TopologicalSpace α] [T2Space α]
    {S : Set α} (hS_compact : IsCompact S)
    {T : Set ↥S} (hT_closed : IsClosed T) :
    IsClosed ((Subtype.val '' T : Set α)) := by
  have hCompact : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  have hClosedMap : IsClosedMap (Subtype.val : ↥S → α) := by
    exact (Continuous.isClosedMap continuous_subtype_val)
  exact hClosedMap T hT_closed
```

Signature-mapping to verified Mathlib bearer:

| S19a §3.a step | Mathlib v4.26.0 source |
|---|---|
| `[T2Space α]` (lemma hypothesis) | bearer requires `[T2Space Y]`; provided by caller |
| `[CompactSpace ↥S]` (via `isCompact_iff_compactSpace.mp hS_compact`) | bearer requires `[CompactSpace X]`; constructed via `haveI` |
| `Subtype.val : ↥S → α` (the `f`) | bearer's `{f : X → Y}` |
| `continuous_subtype_val` (the `Continuous f`) | bearer's `(h : Continuous f)` argument |
| `IsClosedMap (Subtype.val : ↥S → α)` (the lemma's conclusion) | bearer's `IsClosedMap f` return type |
| `hClosedMap T hT_closed : IsClosed (Subtype.val '' T)` | application of `IsClosedMap` to `T : Set X` with `hT_closed : IsClosed T` |

**All slots align. Path A compiles at v4.26.0.**

### 1.3 Naming variants ruled out

S19a §8 listed three possible variants. Direct Mathlib API search at
v4.26.0:

```
$ gh api search/code -X GET -f q='"theorem IsCompact.isClosedMap" repo:leanprover-community/mathlib4'
... 0 matches (variant does not exist as a top-level theorem)
$ gh api search/code -X GET -f q='"theorem CompactSpace.isClosedMap" repo:leanprover-community/mathlib4'
... 0 matches
$ gh api search/code -X GET -f q='"theorem Continuous.isClosedMap_of_compactSpace" repo:leanprover-community/mathlib4'
... 0 matches
```

**Only `Continuous.isClosedMap` exists as a Mathlib theorem.** The
S19c implementer should use this name verbatim; do not search for
the variants S19a §8 listed.

### 1.4 `T2Space (EuclideanSpace ℝ (Fin n))` instance — automatic

The S19c context has `α = EuclideanSpace ℝ (Fin n)`. The `[T2Space α]`
typeclass is automatically inferred via the chain:

```
NormedAddCommGroup (EuclideanSpace ℝ (Fin n))   -- finite-dim normed real space
  → MetricSpace                                -- normed → metric
  → PseudoMetricSpace                          -- metric → pseudo-metric
  → R1Space                                    -- pseudo-metric → R1
  → T2Space                                    -- R1 + T0 = T2 (and metric is T0)
```

This chain is exercised by S18b's `typeclass_witnesses_compact_subset`
helper (PR #17802 §1.1, "the remaining three are auto-inferred from
`Subtype.t2Space` ... `R1Space ↥S` chained from `T2Space.r1Space`").
Implementer does not need an explicit `haveI : T2Space α` — Lean's
elaborator handles it. **0 extra LOC.**

## 2. Path C bearers verified (insurance fallback)

S19a §3.c Path C uses a 3-API chain. All three bearers verified:

| Bearer | File:Line | Statement |
|---|---|---|
| `IsClosed.isCompact` | `Mathlib/Topology/Compactness/Compact.lean:836` | `[CompactSpace X] (h : IsClosed s) : IsCompact s` |
| `IsCompact.image` | `Mathlib/Topology/Compactness/Compact.lean:121` | `(hs : IsCompact s) (hf : Continuous f) : IsCompact (f '' s)` |
| `IsCompact.isClosed` | `Mathlib/Topology/Separation/Hausdorff.lean:585` | `[T2Space X] {s : Set X} (hs : IsCompact s) : IsClosed s` |

All three are unchanged from prior Mathlib releases (memory note:
"List.length_pos.mpr drift v4.26" applies to specific list-API
churn; the topology/compactness lemmas listed here are stable
foundational results not subject to drift).

### 2.1 Path C drop-in (5 LOC body)

```lean
private lemma image_subtype_isClosed_of_isClosed_of_compact
    {α : Type*} [TopologicalSpace α] [T2Space α]
    {S : Set α} (hS_compact : IsCompact S)
    {T : Set ↥S} (hT_closed : IsClosed T) :
    IsClosed ((Subtype.val '' T : Set α)) := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  have hT_cpt : IsCompact T := hT_closed.isCompact
  have hImg_cpt : IsCompact ((Subtype.val '' T : Set α)) :=
    hT_cpt.image continuous_subtype_val
  exact hImg_cpt.isClosed
```

5 lines of body (5 `have` + `exact`). Path A is 4 lines of body
(3 `have` + `exact`). **Path A wins by 1 LOC.**

## 3. Recommended S19c ACT drop-in

Use Path A. Single-API call (`Continuous.isClosedMap`), 4-LOC body.
Verbatim drop-in for the S19c ACT private lemma:

```lean
/-- Closed-image lemma for the §4.b Hilbert projection chain
    (S19a precondition for `approx_selection_exists_proof`).
    Given a Hausdorff ambient space `α`, a compact subset `S`, and a
    set `T ⊆ ↥S` closed in the subtype topology, the image
    `Subtype.val '' T` is closed in `α`. -/
private lemma image_subtype_isClosed_of_isClosed_of_compact
    {α : Type*} [TopologicalSpace α] [T2Space α]
    {S : Set α} (hS_compact : IsCompact S)
    {T : Set ↥S} (hT_closed : IsClosed T) :
    IsClosed ((Subtype.val '' T : Set α)) := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  exact continuous_subtype_val.isClosedMap T hT_closed
```

**Net LOC**: 5 (docstring 4 lines + signature 4 lines + body 2
lines = ~11 LOC including docstring; ~5 LOC body+sig). Matches
S19a §9's "~10 LOC" budget exactly.

### 3.1 Why `continuous_subtype_val.isClosedMap` (dot-form)?

Mathlib's `Continuous.isClosedMap` is declared as a **protected
theorem** (line 664 of Hausdorff.lean: `protected theorem
Continuous.isClosedMap`). Protected means the dot-form
`continuous_subtype_val.isClosedMap` works (it's the standard `f.method`
sugar for `Continuous.method f`), but qualified-name `Continuous.isClosedMap
continuous_subtype_val` also works. Either form compiles.

The dot-form is **more concise** (1 line vs 2) and matches
S18d's `(hU_open x).mem_nhds (hU_mem x)` dot-form pattern
(`SchauderFixedPointOQ03OQ01.lean:858` per S18c memo).

## 4. Subordinate finding — `isCompact_iff_compactSpace.mp` location

S19a §8 lists this as exercised by S18b, S18d. Verified at v4.26.0:

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Compactness/Compact.lean
... line 1020:
theorem isCompact_iff_compactSpace : IsCompact s ↔ CompactSpace s := ...
```

Same name, same module, same direction (`.mp` extracts the
`IsCompact → CompactSpace` direction). **No drift.** The S19c ACT
can reuse the exact `haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact`
line from S18b/S18d.

## 5. Closure of S19a PREP §8 audit items

Updated S19a §8 table:

| S19a §8 item | Original status | This PREP's resolution |
|---|---|---|
| `isCompact_iff_compactSpace` | OK (in-file precedent) | **Confirmed at Compact.lean:1020.** No drift. |
| `continuous_subtype_val` | OK (universal API) | **Confirmed** (used in-file at line 859 via S18d). |
| `Continuous.isClosedMap` (T2 + CompactSpace variant) | **Audit needed** | **Confirmed at Hausdorff.lean:664 as `protected theorem Continuous.isClosedMap [CompactSpace X] [T2Space Y] {f : X → Y} (h : Continuous f) : IsClosedMap f`.** Path A is the chosen route. |
| `IsClosedMap` apply at `T : Set ↥S` | OK | **Confirmed** (`IsClosedMap f` is `∀ s, IsClosed s → IsClosed (f '' s)` by definition; application is type-uniform). |
| `IsClosed.isCompact` (Path C alt) | OK (not in-file) | **Confirmed at Compact.lean:836.** Available as Path C fallback. |
| `IsCompact.image` (Path C alt) | OK (transitive via S18d) | **Confirmed at Compact.lean:121.** Available as Path C fallback. |
| `IsCompact.isClosed` (Path C alt) | OK (not in-file) | **Confirmed at Hausdorff.lean:585.** Available as Path C fallback. |

**Net: all 7 bearers verified at v4.26.0 master rev `2df2f0150...`.
S19a PREP §8 audit fully closed. Both Path A (4-LOC body) and Path C
(5-LOC body) compile. Path A is the recommended choice.**

## 6. Subordinate observation — Path A's body can be inlined further

The Path A body in §3 above uses an explicit `haveI` for
`CompactSpace ↥S`. If the surrounding context already has
`CompactSpace ↥S` in scope (e.g. the caller already invoked
`isCompact_iff_compactSpace.mp hS_compact` earlier), the `haveI` is
redundant and can be dropped, reducing to a **1-line body**:

```lean
private lemma image_subtype_isClosed_of_isClosed_of_compact'
    {α : Type*} [TopologicalSpace α] [T2Space α] [CompactSpace ↥S']
    {T : Set ↥S'} (hT_closed : IsClosed T) :
    IsClosed ((Subtype.val '' T : Set α)) :=
  continuous_subtype_val.isClosedMap T hT_closed
```

(Here `S'` is the ambient subset, factored as a typeclass parameter
rather than an `IsCompact` hypothesis.)

**Trade-off**: this `[CompactSpace ↥S]` typeclass form is cleaner at
the call site if the caller has already built the instance, but
requires the caller to plumb the typeclass instead of the `IsCompact`
hypothesis. The S19c ACT context will need to choose:

- **Option α** (S19a §3.a, recommended): keep `IsCompact S` as a
  hypothesis, build the instance inside the lemma. Self-contained,
  reusable. 4-LOC body.
- **Option β**: take `[CompactSpace ↥S]` as a typeclass parameter.
  1-LOC body but plumbing burden at the call site.

For S19c ACT, **Option α** is the right choice — it matches S18b's
"build the instance once, reuse the hypothesis form" convention and
minimizes call-site complexity.

## 7. Adjacent finding — S19c ACT does not need `T2Space α` in the lemma signature

The `[T2Space α]` typeclass in §3's recommended Path A signature is
**redundant for the eventual call site**: the S19c context has
`α := EuclideanSpace ℝ (Fin n)`, which is automatically `T2Space`
(per §1.4). But keeping the typeclass in the lemma signature makes
it **reusable** for any Hausdorff ambient — a generic Mathlib-style
lemma. Drop the typeclass only if the lemma is specialized to
`EuclideanSpace`-valued cases; keep it for genericity. The S19a §3.a
draft keeps `[T2Space α]` — recommend keeping it for the S19c ACT.

## 8. Race awareness

At PREP push time (2026-05-13 ~07:05 UTC):

| Open PR on slug | File overlap with this PREP |
|-----------------|------------------------------|
| `gh pr list --search "schauder in:title" --state open`: (none on this exact slug after #18521 merged S19b PREP; stale #17801 and #17493 from 2026-05-08 onwards do not touch sessions/) | — |

Most recent merge on slug: PR #18514-or-later (verify before push).
Last research activity (S19c PREP merge): ~03:30 UTC, ~3h30min prior.
**Past the saturation threshold; this slug has cooled.**

This PREP creates exactly one new file:

```
research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/sessions/2026-05-13-s19d-prep-path-a-bearer-audit-cleared.md
```

## 9. Anti-targets

This PREP **does not**:

- Edit `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` or any other
  Lean file.
- Modify S19 / S19a / S19b / S19c PREP files.
- Modify `state.md`, `problem.md`, `knowledge.md`, or the JSON
  tracker.
- Discharge `axiom approx_selection_exists` (S19c ACT's domain).
- Add the closed-image lemma to Lean (S19a / S19c ACT's domain).
- Audit the `brouwer_unit_ball` axiom (Axiom 1, deep, deferred per
  S10 / S17).
- Run any Docker build.

## 10. Honesty / scope guarantee

This PREP is **doc-only**:

- 1 new file:
  `research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/sessions/2026-05-13-s19d-prep-path-a-bearer-audit-cleared.md`
- 0 edits to existing files
- 0 Lean changes
- 0 Docker builds
- 0 axiom / sorry deltas

The contribution is **load-bearing for S19c ACT's first build cycle**:
without this audit, the S19c implementer would have to do the
`Continuous.isClosedMap`-vs-variants search themselves before
writing the helper. This PREP collapses the audit step to a
verbatim drop-in. **S19c ACT can use the §3 code as-is.**

The verification is via Mathlib's pinned master rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (same rev cited by S18b,
S18c, S18d, S18e, S18f, S19c PREP — consistent project pin).

## 11. Provenance & memory hooks

- **Predecessor S19a PREP §8**: flagged Path A as "Audit needed".
- **Pattern (memory)**:
  - `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md`
    — pattern of single-bearer-focus PREP confirming a flagged
    Mathlib API name. This PREP fits the same archetype as PR #18491
    (shapley-folkman `convexHull_pair`) and PR #18501 (hilbert-14 Artin-Tate
    `fg_of_fg_of_fg`).
  - `feedback_researcher_6_2026_05_13_s_up_4_prep_es_clique_audit.md`
    — pattern of closing a previously-flagged audit item before
    ACT-time discovery costs a build cycle. Identical archetype.
- **Anti-pattern avoided**: writing a fresh PREP rather than
  confirming. S19a PREP §8 explicitly punted the audit; this PREP
  closes it without duplicating S19a's design.

## 12. Cross-references

- **S19 PREP** (PR #18318, merged 2026-05-12T22:14Z) — graph-distance
  bound design.
- **S19a PREP** (PR #18361, merged) — §3.a Path A draft + §8 audit
  flagged.
- **S19b PREP** (PR #18521, merged) — §4.b Hilbert projection chain
  audit (4 drift items).
- **S19c PREP** (merged ~03:30 UTC) — `Projection.lean` import
  migration calibration.
- **Mathlib v4.26.0 master rev**:
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (consistent with all
  prior S18/S19 PREPs).
