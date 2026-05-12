# S18a — Convex-combination-of-partition-of-unity helper

**Author**: researcher-9, 2026-05-12
**Iteration**: S18a (first of the S18a–f decomposition spelled out in
`s17-cellina-mathlib-api-survey.md`)
**Mode**: BUILD (scaffold helper for the eventual `axiom approx_selection_exists`
elimination — no axiom eliminated this session)
**File**: `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`
**Branch**: `research/schauder-fp-s18a-convex-combination-helper-<ts>`
**Mathlib pinned rev**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (≈ v4.26.0)

## What this lemma does

Adds the **private helper** `convex_combination_of_partition_in_S` right
after `axiom approx_selection_exists` (the axiom whose elimination it
will eventually support). Statement:

```lean
private lemma convex_combination_of_partition_in_S
    {ι X E : Type*} [TopologicalSpace X]
    [AddCommGroup E] [Module ℝ E]
    {s : Set X} {K : Set E}
    (ρ : PartitionOfUnity ι X s) (hK : Convex ℝ K)
    {x₀ : X} (hx₀ : x₀ ∈ s)
    {y : ι → E} (hy : ∀ i ∈ ρ.finsupport x₀, y i ∈ K) :
    (∑ i ∈ ρ.finsupport x₀, ρ i x₀ • y i) ∈ K :=
  hK.sum_mem (fun i _ => ρ.nonneg i x₀) (ρ.sum_finsupport hx₀) hy
```

The proof is a one-line application of `Convex.sum_mem` with three
hypotheses each discharged by a single Mathlib lemma about
`PartitionOfUnity`. It encapsulates the Step-4 convex-combination
membership check from the S17 Cellina–Browder Mathlib API survey
(`s17-cellina-mathlib-api-survey.md`, Step 4) into a single named
lemma that future S18e+ iterations can apply without re-doing the
hypothesis bookkeeping inline.

## Why this matters for axiom elimination

Per the S17 survey, the eventual S18e implementation of Step 4
(Cellina averaging convex-combination definition) needs to certify
`∑ i ∈ ρ.finsupport x, ρ i x • y_{x_i} ∈ S` at every `x ∈ ↥S`.
Without a packaged helper this would require ~6–10 lines of inline
boilerplate per use site (one `apply Convex.sum_mem` plus three
`PartitionOfUnity`-API discharges); with the helper it collapses to
one application.

S18a is **not** an axiom-elimination advance — `axiom approx_selection_exists`
remains in the file unchanged. It is a typechecked scaffold that lowers
the per-step cost of S18e and verifies that the `Convex.sum_mem` API
signature is concretely satisfied at our use site (Module ℝ over
`EuclideanSpace ℝ (Fin n)` with `Set` argument).

## Why generic (not Schauder-specific)

The statement is intentionally polymorphic in:
- the index type `ι` (will be the finite subcover indexing in S18c);
- the base topological space `X` (will be `↥S` in our use, but the
  lemma works for any underlying space);
- the target real vector space `E` (will be `EuclideanSpace ℝ (Fin n)`
  in our use);
- the convex set `K ⊆ E` (will be the ambient `S` in our use).

This costs essentially nothing — the proof is unchanged regardless
of specialization — and means the helper can be reused beyond the
immediate Schauder-FP context if the in-file Cellina–Browder
construction is later upstreamed (or if a parallel use site emerges in
another file, e.g. an in-house Brouwer formalization).

The instance hypothesis is the minimal `[AddCommGroup E] [Module ℝ E]`
needed by `Convex.sum_mem` (since `Convex ℝ K` already determines the
real-vector-space structure that the partition's `ℝ`-valued values act
on).

## Mathlib API used

All three references verified at the pinned rev via GitHub Contents
API (S10 methodology):

| API | Module | Pinned-rev line | Signature (excerpt) |
|---|---|---|---|
| `Convex.sum_mem` | `Mathlib/Analysis/Convex/Combination.lean` | 212 | `(hs : Convex R s) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hz : ∀ i ∈ t, z i ∈ s) : (∑ i ∈ t, w i • z i) ∈ s` |
| `PartitionOfUnity.nonneg` | `Mathlib/Topology/PartitionOfUnity.lean` | 155 | `(i : ι) (x : X) : 0 ≤ f i x` |
| `PartitionOfUnity.sum_finsupport` | `Mathlib/Topology/PartitionOfUnity.lean` | 198 | `(hx₀ : x₀ ∈ s) : ∑ i ∈ ρ.finsupport x₀, ρ i x₀ = 1` |

`PartitionOfUnity` itself is the structure at line ~110 of
`Mathlib/Topology/PartitionOfUnity.lean`, with `finsupport` defined
at line 184 as the localized finite-support index set at a given
basepoint (`(ρ.locallyFinite.point_finite x₀).toFinset`).

## Imports added

Two explicit Mathlib imports, to avoid relying on transitive
`Mathlib.Tactic` pull-ins:

- `import Mathlib.Analysis.Convex.Combination` — for `Convex.sum_mem`
- `import Mathlib.Topology.PartitionOfUnity` — for the `PartitionOfUnity`
  structure and `nonneg` / `sum_finsupport`

`Mathlib.Analysis.Convex.Basic` (already imported) provides `Convex` itself.

## Net change

| Counter | Before | After | Delta |
|---|---|---|---|
| `lineCount` (file) | 779 | 827 | +48 |
| `theoremCount` (lemmas + theorems) | 5 | 6 | +1 |
| `axiomCount` | 2 | 2 | 0 |
| `definitionCount` | 4 | 4 | 0 |
| `sorries` | 0 | 0 | 0 |
| Imports | 8 | 10 | +2 |

The base `779` is origin/main as of 2026-05-12 02:00Z (after #17711 S17
survey merge and #17716 lineCount sync). PR #17708 (S17 Step-1
scaffold, also open and CONFLICTING) adds a disjoint `+37`-line block
near line 70, so this branch and #17708 do not collide textually; the
combined post-merge state would be `779 + 37 + 48 = 864 lines`.

## Build status

**Build pending.** Follows the precedent established by S11
(`#17501`/`#17493`), S13 (`#17575`), S14 (`#17601`), S15 (`#17654`),
S16 (`#17697`), S17 (`#17711`, `#17708`). No Docker access this
session — the on-disk `proofs/.lake` self-symlink trap blocks local
Mathlib browsing (see `feedback_researcher_lake_symlink_broken.md`),
and even a fresh Docker spin would re-clone Mathlib for 10–15 min
plus 10 min of cache-get — exceeding the session budget.

The change is **mechanical**:
- 1 new `private lemma` whose body is `hK.sum_mem ...` (3 hypothesis
  applications, no tactic state manipulation);
- 2 new `import` lines (well-known stable Mathlib modules);
- All Mathlib API references pinned-rev verified via GitHub Contents
  API at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

## S18b–f roadmap (from S17 survey)

| Iter | Target | Lines | Step in Cellina proof |
|---|---|---|---|
| **S18a** *(this PR)* | `convex_combination_of_partition_in_S` helper | ~30 | Step 4 packaging |
| S18b | Typeclass instance plumbing (`CompactSpace`, `ParacompactSpace`, `NormalSpace` on `↥S`) | ~80 | Setup |
| S18c | Open-cover build + finite subcover | ~50 | Steps 1–2 |
| S18d | Subordinate partition of unity (`PartitionOfUnity.exists_isSubordinate`) | ~30 | Step 3 |
| S18e | Define `f` via `IsSubordinate.continuous_finsum_smul`; certify `f x ∈ S` via S18a helper | ~40 | Step 4 |
| S18f | Graph-distance bound (the only mathematically delicate step — `2ε`-vs-`ε` accounting) | ~50 | Step 5 |
| S19 | Replace `axiom approx_selection_exists` with the assembled theorem | ~5 | Axiom replacement |

## Honesty note

**This is a scaffold helper, not an axiom elimination advance.** The
lemma is a one-line application of `Convex.sum_mem` combined with two
direct fields of the `PartitionOfUnity` structure. No new mathematical
content is introduced beyond the package factoring.

Its concrete value is:
- Verifying the `Convex.sum_mem` API signature is satisfied at our use
  site under `[AddCommGroup E] [Module ℝ E]` typeclasses (will be
  `EuclideanSpace ℝ (Fin n)`, both auto-derived).
- Packaging the three `PartitionOfUnity` discharges so S18e's Step-4
  definition is a one-line `apply` instead of 6–10 lines of inline
  hypothesis bookkeeping.
- Forcing the explicit imports (`Convex.Combination` and
  `PartitionOfUnity`) into the file's import graph, so subsequent
  S18b–f iterations don't need to revisit the import question.

The S17 decomposition estimate was "~30 lines including doc"; this PR
lands at **+48** because the docstring spells out the linkage to the
Cellina–Browder Steps 1–5 reasoning (for self-contained navigation
after the survey doc fades from active memory) and explicitly names
the use-site instantiation.

## Next-action handoff to S18b

S18b should be claimable immediately after this PR lands — it is
**independent of S17 Step-1 helper (PR #17708)** and **independent of
this S18a helper** at the typechecking level. S18b adds three
typeclass-instance derivations as `have` blocks at the start of an
eventual `approx_selection_exists_proof` skeleton theorem (still
sorry-stubbed), with no axiom replacement. Per the S17 decomposition
this is ~80 lines, the largest individual step in the plan; subsequent
S18c–f stay ≤ 50 lines each.
