# S18b — Typeclass instance plumbing scaffold

**Author**: researcher-11, 2026-05-12
**Iteration**: S18b (second of the S18a–f decomposition spelled out in
`s17-cellina-mathlib-api-survey.md`)
**Mode**: BUILD (scaffold helper for the eventual `axiom approx_selection_exists`
elimination — no axiom eliminated this session)
**File**: `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`
**Branch**: `research/schauder-fp-s18b-typeclass-plumbing-<ts>`
**Mathlib pinned rev**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (≈ v4.26.0)

## What this lemma does

Adds the **private helper** `typeclass_witnesses_compact_subset` right
after the S18a helper `convex_combination_of_partition_in_S`. Statement:

```lean
private lemma typeclass_witnesses_compact_subset {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS_compact : IsCompact S) :
    CompactSpace ↥S ∧ T2Space ↥S ∧ NormalSpace ↥S ∧ ParacompactSpace ↥S := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
```

The four-typeclass derivation packages exactly one explicit step
(`CompactSpace ↥S` via `isCompact_iff_compactSpace.mp`); the remaining
three instances are picked up by Lean's typeclass inference once the
single `haveI` is in scope.

## Why this matters for axiom elimination

Per the S17 survey, the eventual S18c–f construction of
`approx_selection_exists_proof` needs the following four instances on
`↥S` (the compact convex domain of `F`):

- **`CompactSpace ↥S`** — required by `IsCompact.elim_nhds_subcover`
  for the Step-2 finite-subcover extraction; the natural form of the
  Cellina–Browder argument operates on the type `↥S` rather than on
  `S` as a `Set` predicate.
- **`T2Space ↥S`** — implicit hypothesis of
  `PartitionOfUnity.exists_isSubordinate`.
- **`NormalSpace ↥S`** — required for the
  `PartitionOfUnity.exists_isSubordinate` construction (Mathlib's
  partition-of-unity API needs normality of the base space, which is
  why compact T2 is the standard sufficient setting).
- **`ParacompactSpace ↥S`** — same reason; many partition-of-unity
  lemmas in Mathlib are stated under `ParacompactSpace`, which is the
  weaker hypothesis that holds here automatically (compact ⇒
  paracompact).

Without confirming these instances are derivable at the pinned
Mathlib rev, S18c–f could each silently bake in a redundant
`haveI`/`inferInstance` discovery step or — worse — discover at
implementation time that some chain has shifted and the partition-of-
unity API call no longer typechecks. This lemma is the safety check
that establishes, **once and centrally**, that the entire required
typeclass cluster is one `haveI` away.

## Mathlib API used (all pinned-rev verified via GitHub Contents API)

| API | Module | Pinned-rev line | Role |
|---|---|---|---|
| `isCompact_iff_compactSpace` | `Mathlib/Topology/Compactness/Compact.lean` | 989 | `IsCompact s ↔ CompactSpace s` |
| `Subtype.t2Space` (instance) | `Mathlib/Topology/Separation/Hausdorff.lean` | 351 | `[T2Space X] → T2Space (Subtype p)` |
| `T2Space.r1Space` (instance) | `Mathlib/Topology/Separation/Hausdorff.lean` | 120 | `[T2Space X] → R1Space X` |
| `NormalSpace.of_compactSpace_r1Space` (instance) | `Mathlib/Topology/Separation/Regular.lean` | 489 | `[CompactSpace X] [R1Space X] → NormalSpace X` |
| `paracompact_of_compact` (instance) | `Mathlib/Topology/Compactness/Paracompact.lean` | 180 | `[CompactSpace X] → ParacompactSpace X` |

Each verified via `curl https://api.github.com/repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c…`.

## Inference chain

Starting from the explicit hypothesis `hS_compact : IsCompact S` and
the ambient `EuclideanSpace ℝ (Fin n)` (which is `T2Space` via its
metric structure, automatic at module-load time):

```
hS_compact : IsCompact S
   │
   │ isCompact_iff_compactSpace.mp
   ▼
[CompactSpace ↥S]                       ← explicit haveI
   │
   ├──► T2Space ↥S        via Subtype.t2Space   (auto from ambient T2)
   │       │
   │       │ T2Space.r1Space
   │       ▼
   │     R1Space ↥S
   │       │
   │       │ NormalSpace.of_compactSpace_r1Space  (needs CompactSpace + R1Space)
   │       ▼
   │     NormalSpace ↥S
   │
   └──► ParacompactSpace ↥S    via paracompact_of_compact  (needs CompactSpace)
```

The first chain branch handles (T2, Normal); the second handles
Paracompact. Both are entirely typeclass-driven once `CompactSpace ↥S`
is registered as a local instance via `haveI`.

## Why generic (`{n : ℕ}` rather than fixed)

Following the S18a convention: the statement quantifies over `n`
rather than fixing it, so the helper is reusable across any Euclidean
ambient dimension. The Cellina–Browder construction is naturally
polymorphic in the ambient dimension, so this matches the eventual
use site's signature.

## Independent S18-prep finding

The state.md (pre-S18b) listed an action item from the S17 survey:

> Read lines 69–89 of `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`
> to confirm whether `IsUpperHemicontinuous` quantifies over
> ambient-image open sets or subtype-relative open sets.

**Resolved (S18b):** Line 71–73 of the file:

```lean
def IsUpperHemicontinuous {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (F : SetValuedMap X Y) : Prop :=
  ∀ V : Set Y, IsOpen V → IsOpen {x | F x ⊆ V}
```

`IsOpen V` is interpreted in the topology of `Y`. When we instantiate
`Y := ↥S`, `Y` already carries the **subtype topology**, so `V` ranges
over **subtype-relative** open sets. Therefore S17's
`uhc_local_thickening` (PR #17708) — which calls `hF _
Metric.isOpen_thickening` with `V := Metric.thickening ε (F x₀)` in the
ambient topology of `Y` — is **directly applicable** in the eventual
`approx_selection_exists_proof`, because when `Y = ↥S` the
`Metric.thickening` is taken in the subtype `↥S` (which is itself a
`PseudoMetricSpace` via `Subtype.pseudoMetricSpace`). No additional
preimage-pull step is required in S18c.

## Imports added

None. `Subtype.t2Space`, `NormalSpace.of_compactSpace_r1Space`, and
`paracompact_of_compact` are picked up transitively through the
existing imports (`Mathlib.Analysis.InnerProductSpace.EuclideanDist`
pulls topological-group infrastructure including the separation
hierarchy; `Mathlib.Topology.PartitionOfUnity` from S18a already pulls
`Mathlib.Topology.Compactness.Paracompact`). `isCompact_iff_compactSpace`
is in `Mathlib.Topology.Compactness.Compact`, also transitive.

## Net change

| Counter | Before | After (post-S18b only) | After (post-S18b + meta sync) | Delta (post-S18b only) |
|---|---|---|---|---|
| `lineCount` (file)                 | 864 | 907 | 907 | +43 |
| `theoremCount` (lemmas + theorems) | 7   | 8   | 8   | +1  |
| `axiomCount`                       | 2   | 2   | 2   | 0   |
| `definitionCount`                  | 4   | 4   | 4   | 0   |
| `sorries`                          | 0   | 0   | 0   | 0   |
| Imports                            | 10  | 10  | 10  | 0   |

The base `864` is origin/main as of 2026-05-12 03:21Z (after #17708
S17 Step-1 scaffold merge and #17755 S18a helper merge).

### Meta sync component

The current `meta.json` (pre-S18b) is stale at `lineCount=827`,
`theoremCount=6`, with only 7 of 10 imports — values that reflect the
post-#17755 (S18a) state but were not updated through the #17708 (S17
Step-1) merge. Both gallery `meta.json` (top-level `meta` block and
`leanFile` block) and `originalContributions` are brought to the
post-S18b state in the same PR:

- `lineCount`: 827 → **907**
- `theoremCount`: 6 → **8**
- `imports`: 7 entries → **10** (adds
  `Mathlib.Analysis.InnerProductSpace.Projection`,
  `Mathlib.Analysis.Convex.Combination`,
  `Mathlib.Topology.PartitionOfUnity`).
- `originalContributions`: adds three new entries for `uhc_local_thickening`
  (S17 Step-1, PR #17708), `convex_combination_of_partition_in_S`
  (S18a, PR #17755), and `typeclass_witnesses_compact_subset` (S18b,
  this PR).

## Build status

**Build pending.** Follows the precedent established by S11
(`#17501`/`#17493`), S13 (`#17575`), S14 (`#17601`), S15 (`#17654`),
S16 (`#17697`), S17 (`#17711`, `#17708`), S18a (`#17755`). No Docker
access this session — the on-disk `proofs/.lake` self-symlink trap
blocks local Mathlib browsing (see
`feedback_researcher_lake_symlink_broken.md`), and even a fresh Docker
spin would re-clone Mathlib for 10–15 min plus 10 min of cache-get —
exceeding the session budget.

The change is **mechanical**:
- 1 new `private lemma` whose body is `haveI` + 4× `inferInstance`;
- 0 new `import` lines;
- All Mathlib API references pinned-rev verified via GitHub Contents
  API at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

The principal risk would be if one of the three auto-instances had
been moved/renamed since the pinned rev — but the GitHub-API lookups
verify them at the *exact* pinned rev, so this risk reduces to "the
local `.lake` would resolve identically." All four lookups confirm
the instances are explicitly `instance`-marked (priority 100, all
auto-inferable).

## S18b–f roadmap (from S17 survey, updated)

| Iter | Target | Lines | Step in Cellina proof | Status |
|---|---|---|---|---|
| **S18a** | `convex_combination_of_partition_in_S` helper | ~30 | Step 4 packaging | ✅ merged #17755 |
| **S18b** *(this PR)* | `typeclass_witnesses_compact_subset` (CompactSpace/T2Space/NormalSpace/ParacompactSpace on ↥S) | ~80 | Setup | this PR |
| S18c | Open-cover build + finite subcover (`exists_finite_subcover_for_uhc`) | ~50 | Steps 1–2 | next |
| S18d | Subordinate partition of unity (`PartitionOfUnity.exists_isSubordinate`) | ~30 | Step 3 | |
| S18e | Define `f` via `IsSubordinate.continuous_finsum_smul`; certify `f x ∈ S` via S18a helper | ~40 | Step 4 | |
| S18f | Graph-distance bound (the only mathematically delicate step — `2ε`-vs-`ε` accounting) | ~50 | Step 5 | |
| S19 | Replace `axiom approx_selection_exists` with the assembled theorem | ~5 | Axiom replacement | |

## Honesty note

**This is a scaffold helper, not an axiom elimination advance.** The
lemma is a single `haveI` + four `inferInstance` calls. No new
mathematical content is introduced beyond the package factoring and
the pinned-rev verification of the typeclass chain.

Its concrete value is:

- Verifying the four-typeclass derivation succeeds at the pinned
  Mathlib rev (catches any silent inference-chain shift before
  S18c–f).
- Documenting the inference chain so subsequent iterations don't need
  to re-discover which instance is auto-derived and which needs
  `haveI`.
- Resolving the S17 survey's outstanding question about
  `IsUpperHemicontinuous` quantifier convention (subtype-relative,
  not ambient — `uhc_local_thickening` is directly reusable in S18c).

The `axiom approx_selection_exists` remains unchanged. Its replacement
remains in S18f (graph-distance accounting) and S19 (assembly).
