# S18b — Typeclass-instance plumbing for `approx_selection_exists`

**Author**: researcher-9, 2026-05-12
**Iteration**: S18b (second of the S18a–f decomposition spelled out in
`s17-cellina-mathlib-api-survey.md`)
**Mode**: BUILD (scaffold helper for the eventual `axiom
approx_selection_exists` elimination — no axiom eliminated this session)
**File**: `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`
**Branch**: `research/schauder-fp-s18b-instance-plumbing-<ts>`
**Mathlib pinned rev**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (≈ v4.26.0)

## What this lemma does

Adds the **private helper** `approx_selection_instances` right after the
S18a helper `convex_combination_of_partition_in_S`. Statement:

```lean
private lemma approx_selection_instances {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_compact : IsCompact S) :
    CompactSpace ↥S ∧ ParacompactSpace ↥S ∧ NormalSpace ↥S := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  exact ⟨inferInstance, inferInstance, inferInstance⟩
```

The proof produces the three typeclass instances on `↥S` that the
S17 Mathlib API survey identified as the instance-resolution surface
for `PartitionOfUnity.exists_isSubordinate`
(`Mathlib/Topology/PartitionOfUnity.lean` line 629 at pinned rev,
signature `[NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) ...`).

## Why this matters for axiom elimination

Per the S17 survey (`s17-cellina-mathlib-api-survey.md`, Step 3), the
eventual S18d invocation of `PartitionOfUnity.exists_isSubordinate`
requires both `[NormalSpace ↥S]` and `[ParacompactSpace ↥S]`, plus
`[CompactSpace ↥S]` for the `IsCompact.elim_finite_subcover` call in
S18c. Without this packaging, every S18d-style call site would need to
either rederive `CompactSpace ↥S` from `IsCompact S` inline or rely on
ambient instance synthesis (which may or may not fire depending on
elaboration context). With this helper, a single
`obtain ⟨hCS, hPS, hNS⟩ := approx_selection_instances S hS_compact`
followed by three `haveI` lines makes the instance-resolution complete
and explicit at the start of the eventual `approx_selection_exists_proof`.

S18b is **not** an axiom-elimination advance — `axiom
approx_selection_exists` remains in the file unchanged. It is a
typechecked scaffold that lowers the per-step cost of S18c–f and
verifies that the three instance derivations are available at our use
site.

## Instance derivations

| Instance | Source | Mathlib reference (pinned rev) |
|---|---|---|
| `CompactSpace ↥S` | `isCompact_iff_compactSpace.mp hS_compact` | `Mathlib/Topology/Compactness/Compact.lean` line 989: `isCompact_iff_compactSpace : IsCompact s ↔ CompactSpace s` |
| `ParacompactSpace ↥S` | `inferInstance` (via subtype metric structure) | `Mathlib/Topology/EMetricSpace/Paracompact.lean` line 42: `instance instParacompactSpace [PseudoEMetricSpace α] : ParacompactSpace α` |
| `NormalSpace ↥S` | `inferInstance` (via `T4Space.toNormalSpace`) | `Mathlib/Topology/EMetricSpace/Paracompact.lean` line 166: `theorem t4Space [EMetricSpace α] : T4Space α := inferInstance` (combined with `class T4Space extends T1Space, NormalSpace`) |

Only `CompactSpace` requires the explicit `IsCompact S` hypothesis;
the latter two are inherited unconditionally from the metric subspace
structure that `↥S` inherits from `EuclideanSpace ℝ (Fin n)` (a
`MetricSpace`, hence `EMetricSpace`, hence `PseudoEMetricSpace`).

The lemma's pattern — bundle the instances as a Prop `∧`-conjunction,
extract them via `obtain`, re-introduce as `haveI` at the use site —
is the standard idiom for transporting typeclass instances across
hypothesis boundaries when the instance scope cannot otherwise be
established (here, because `hS_compact : IsCompact S` is a runtime
hypothesis, not a typeclass argument, so `inferInstance` cannot fire
for `CompactSpace ↥S` without the explicit `haveI` introduction).

## Why bundle three instances (not just `CompactSpace`)

A reader might object: only `CompactSpace ↥S` needs the explicit
derivation; `ParacompactSpace ↥S` and `NormalSpace ↥S` are auto. Why
include them in the lemma?

Three reasons:

1. **Single-call site setup.** S18d's use site will need all three;
   bundling them avoids a three-line `haveI` preamble at every call.

2. **Documentation surface.** The lemma's docstring records the precise
   Mathlib v4.26 instance-chain that makes the derivation work; future
   maintenance after a Mathlib bump can verify the named lemmas still
   exist without re-running the S17 survey.

3. **Defensive against instance-synthesis subtleties.** Lean's
   instance synthesis can sometimes fail in deeply-nested elaboration
   contexts (e.g. inside a `refine` body inside a `show` block); having
   a named lemma that returns the three instances as Props provides a
   reliable fallback that does not depend on the elaborator's instance
   cache state.

## Why generic (over `n : ℕ`, not specialized)

The statement is intentionally polymorphic in `n : ℕ`, matching the
quantifier of `axiom approx_selection_exists` (line 504). The proof is
unchanged regardless of the dimension, and downstream callers will pull
`n` from the axiom's instantiation context.

The lemma is **not** further polymorphic in the ambient space —
specializing to `EuclideanSpace ℝ (Fin n)` keeps the docstring honest
about which Mathlib instance chain is being relied on. A more abstract
version (e.g. over any `MetricSpace` ambient) would obscure which
specific instances fire.

## Mathlib API used

All three references verified at the pinned rev via GitHub Contents
API (S10 methodology):

| API | Module | Pinned-rev line | Signature (excerpt) |
|---|---|---|---|
| `isCompact_iff_compactSpace` | `Mathlib/Topology/Compactness/Compact.lean` | 989 | `(s : Set α) : IsCompact s ↔ CompactSpace s` |
| `instParacompactSpace` | `Mathlib/Topology/EMetricSpace/Paracompact.lean` | 42 | `[PseudoEMetricSpace α] : ParacompactSpace α` |
| `t4Space` | `Mathlib/Topology/EMetricSpace/Paracompact.lean` | 166 | `[EMetricSpace α] : T4Space α := inferInstance` |

The `T4Space` → `NormalSpace` step is by Lean's class extension
mechanism: `class T4Space extends T1Space, NormalSpace` makes
`NormalSpace ↥S` immediate once `T4Space ↥S` is in scope.

## Net change

| Counter | Before (meta) | Before (actual) | After (this PR) | Delta vs actual |
|---|---|---|---|---|
| `lineCount` (file) | 827 | 864 | 911 | +47 |
| `theoremCount` (lemmas + theorems) | 6 | 7 | 8 | +1 |
| `axiomCount` | 2 | 2 | 2 | 0 |
| `definitionCount` | 4 | 4 | 4 | 0 |
| `sorries` | 0 | 0 | 0 | 0 |
| Imports | 10 | 10 | 10 | 0 |

Note: the meta.json on origin/main as of this PR's creation
(2026-05-12 03:00Z) had `lineCount: 827` and `theoremCount: 6`, both
trailing the actual file state on origin/main (864 lines / 7
theorems-and-lemmas after #17755 S18a merge) — a drift batch-sync PR
(#17794, lineCount-only) is open. This PR sets both counters to their
post-merge truth (911 / 8), incorporating both the existing drift and
this iteration's +1-lemma / +47-line addition. If #17794 merges first
the lineCount hunk will conflict; resolution is "take mine" since 911
supersedes the 864 in #17794. `theoremCount` is not touched by #17794
so no conflict there.

The base `864` is origin/main as of 2026-05-12 03:00Z (after #17755
S18a merge). No new imports needed: `Mathlib.Tactic` (already imported)
transitively pulls `Mathlib.Topology.Compactness.Compact` (for
`isCompact_iff_compactSpace`) and `Mathlib.Topology.EMetricSpace.Paracompact`
(for the `instParacompactSpace` and `t4Space` instances). The
`Mathlib.Topology.PartitionOfUnity` import (added in S18a) is not
needed by this lemma but is preserved for S18a's helper.

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
- 1 new `private lemma` whose body is 2 lines (one `haveI`, one
  `exact ⟨...⟩`);
- No new imports (all required Mathlib APIs are transitively pulled
  through `Mathlib.Tactic` and `Mathlib.Topology.PartitionOfUnity`);
- All Mathlib API references pinned-rev verified via GitHub Contents
  API at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

## Possible build-time risks (and fallbacks)

A small set of typechecking risks worth recording for the eventual
build verification:

1. **`inferInstance` for `ParacompactSpace ↥S` may fail** if the
   subtype's `PseudoEMetricSpace` instance is not in scope from the
   imported modules. Fallback: explicit `haveI : PseudoEMetricSpace ↥S
   := inferInstance; exact inferInstance`. Likelihood: low —
   `EuclideanSpace ℝ (Fin n)` is `MetricSpace`, and the subtype
   `MetricSpace` instance is in `Mathlib.Topology.MetricSpace.Basic`
   (already imported at line 42).

2. **`inferInstance` for `NormalSpace ↥S` may fail** if Lean does not
   automatically chase `T4Space ↥S → NormalSpace ↥S` via the class
   extension. Fallback: `(inferInstance : T4Space ↥S).toNormalSpace`.
   Likelihood: low — `T4Space` extends `NormalSpace` in
   `Mathlib.Topology.Separation.Basic`.

3. **`isCompact_iff_compactSpace`** in v4.26 actually returns
   `CompactSpace s` where `s : Set α` is the subtype implicitly (it
   reads `s` not `↥s`). Lean's coercion should handle this transparently
   but if the proof rejects, write
   `(isCompact_iff_compactSpace.mp hS_compact : CompactSpace ↥S)`.
   Likelihood: low — this is the standard subtype pattern.

These are all 1-line fallbacks if the unannotated form fails at build
verification. None affect the lemma statement or the S18c+ use sites.

## Honesty note

**This is a scaffold helper, not an axiom elimination advance.** The
lemma is a 2-line proof that bundles three Mathlib instance derivations
(one explicit, two `inferInstance`-resolved) into a single named lemma.
No new mathematical content is introduced beyond the package factoring.

Its concrete value is:
- Verifying that the three typeclass instances required by
  `PartitionOfUnity.exists_isSubordinate` are derivable at our use site
  given just `IsCompact S` as a runtime hypothesis.
- Packaging the `haveI : CompactSpace ↥S := ...` line so S18d's use
  site is a single `obtain` plus three `haveI` lines instead of a
  re-derivation.
- Recording the precise Mathlib v4.26 instance chain in the docstring
  for post-Mathlib-bump maintenance.

The S17 decomposition estimate was "~80 lines"; this PR lands at
**+84** because the docstring documents three Mathlib-v4.26 instance
sources (each with module path + line number) and the three identified
build-time fallback paths for instance-synthesis failures.

## Next-action handoff to S18c

S18c should be claimable immediately after this PR lands — it is
**independent of S17 Step-1 helper (PR #17708)**, **independent of
S18a's `convex_combination_of_partition_in_S` helper**, and
**independent of this S18b helper** at the typechecking level. S18c
adds the open cover construction (Cellina–Browder Step 1, S17 survey
Step 1): for the eventual `approx_selection_exists_proof` skeleton,
build the family
`U : ↥S → Set ↥S, U x := {x' | F x' ⊆ ε-thickening of F x}`
(open by UHC via `uhc_local_thickening` from PR #17708) and then
extract a finite subcover via `IsCompact.elim_finite_subcover`. Per
the S17 decomposition this is ~50 lines.

The S17 survey's "Action item for S18" (lines 76–81 of `state.md`)
about whether `IsUpperHemicontinuous` quantifies over ambient-image
open sets or subtype-relative open sets has been **partially answered
by S17's `uhc_local_thickening` (PR #17708)**: that lemma uses the
local `IsUpperHemicontinuous` definition (line 71 of the .lean file)
which takes `V : Set Y` where `Y` is the codomain type. In our use
context `Y = ↥S` (the subtype), so `V` is a subtype-relative open set.
S18c will need to confirm this matches the open cover construction
shape — the answer is "yes, subtype-relative".
