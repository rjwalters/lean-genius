# S18c — Open-cover + finite-subcover packaging (Cellina–Browder Steps 1–2)

**Author**: researcher-3, 2026-05-12
**Iteration**: S18c
**Mode**: ACT (build pending — Docker build deferred to CI; the two
new Mathlib API references re-verified at pinned rev via GitHub
Contents API)
**File**: `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`
**Target axiom (eventual)**: `approx_selection_exists` (Cellina–Browder
graph form, line 504)
**Mathlib pinned rev**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

## What landed

A single private helper lemma `exists_finite_subcover_for_uhc`
(50 lines counting the docstring) discharging Steps 1 and 2 of the
Cellina–Browder construction in one go:

```lean
private lemma exists_finite_subcover_for_uhc {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS_compact : IsCompact S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_uhc : IsUpperHemicontinuous F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : ↥S → Set ↥S, ∃ s : Finset ↥S,
      (∀ x : ↥S, IsOpen (U x)) ∧
      (∀ x : ↥S, x ∈ U x) ∧
      (∀ x z : ↥S, z ∈ U x → F z ⊆ Metric.thickening ε (F x)) ∧
      (⋃ x ∈ s, U x = (⊤ : Set ↥S))
```

### Proof structure

Three tactic blocks; the loadbearing line is `choose`:

1. `haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact`
   — same line as `typeclass_witnesses_compact_subset` (S18b).
   Materialises the typeclass instance needed in step 3.

2. `choose U hU_open hU_mem hU_sub using fun x : ↥S =>
   uhc_local_thickening hF_uhc x ε hε`
   — pointwise application of S17's
   `uhc_local_thickening` (PR #17708) to every base point `x : ↥S`.
   Lean's `choose` tactic produces:
   - `U : ↥S → Set ↥S`
   - `hU_open : ∀ x, IsOpen (U x)`
   - `hU_mem : ∀ x, x ∈ U x`
   - `hU_sub : ∀ x z, z ∈ U x → F z ⊆ Metric.thickening ε (F x)`

3. `obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover U (fun x =>
   (hU_open x).mem_nhds (hU_mem x))`
   — extracts a finite subcover via Mathlib's `CompactSpace` API
   (`Mathlib.Topology.Compactness.Compact` L763).

4. `exact ⟨U, s, hU_open, hU_mem, hU_sub, hs⟩`
   — repackage the four facts plus the cover equation.

## Mathlib API re-verification

Both Mathlib lemma references re-confirmed at pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via GitHub Contents API.

### `isCompact_iff_compactSpace`
`Mathlib/Topology/Compactness/Compact.lean` L989:
```lean
theorem isCompact_iff_compactSpace : IsCompact s ↔ CompactSpace s
```
`.mp` direction: `IsCompact S → CompactSpace ↥S`. Same site as S18b's
`typeclass_witnesses_compact_subset`. No drift between S18b and S18c
(both verified at the same rev).

### `CompactSpace.elim_nhds_subcover`
`Mathlib/Topology/Compactness/Compact.lean` L763:
```lean
theorem CompactSpace.elim_nhds_subcover [CompactSpace X]
    (U : X → Set X) (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset X, ⋃ x ∈ t, U x = ⊤
```
Used directly with the `nhds` membership built from `hU_open` and
`hU_mem` via `IsOpen.mem_nhds`. The output equation `⋃ x ∈ t, U x = ⊤`
matches the `(⊤ : Set ↥S)` clause in the lemma statement.

## Why include the full ↥S-indexed `U` (not just the finite Finset)

`PartitionOfUnity.exists_isSubordinate`
(`Mathlib.Topology.PartitionOfUnity` L433) takes an indexed family
`U : ι → Set X` with `s ⊆ ⋃ i, U i`. For S18d's invocation:

* If the implementer prefers `ι = ↥S` (full family), the cover
  hypothesis `Set.univ ⊆ ⋃ x : ↥S, U x` follows from `hU_mem x`
  via `Set.subset_iUnion` (one-line chase).
* If the implementer prefers `ι = ↑(s : Finset ↥S)` (the finite
  subcover), the cover hypothesis follows directly from the
  `⋃ x ∈ s, U x = ⊤` equation, after restricting to the Finset's
  index type.

Returning both lets S18d (and S18e) pick whichever index set is
ergonomically lighter, without re-deriving the family from
`uhc_local_thickening` a second time.

## Independent S17-followup compatibility

PR #17800 (open at time of writing; researcher-8, doc-only) resolved
the `IsUpperHemicontinuous` quantifier-signature gating question by
confirming that `uhc_local_thickening` applies directly at `Y = ↥S`
with no preimage pull-back step. S18c's proof exercises this
resolution operationally — the second tactic block invokes
`uhc_local_thickening hF_uhc x ε hε` where `hF_uhc :
IsUpperHemicontinuous (F : SetValuedMap (↥S) (↥S))`. Successful Lean
typechecking of this single line is the practical confirmation that
the S17-followup analysis is correct.

If PR #17800 lands before this PR, there will be a state.md merge
conflict in the "Independent S18-prep" / iteration history sections;
both PRs add information in the same neighbourhood. The conflict is
docs-only and resolvable by keeping both sections side by side.

## Honest scope statement

**S18c does not eliminate any axiom.** It is the third of the six
S18a–f scaffolding PRs (per the S17 survey's 6-step decomposition,
sized to keep each PR ≤ 80 lines and independent of prior PR builds).
The deliverable is:

* One new private lemma packaging Cellina–Browder Steps 1–2 (50 lines
  including 30-line docstring).
* `meta.json` `lineCount` and `theoremCount` sync (907→957, 8→9).
* `state.md` history row + reference-files index entry.
* This session note documenting the proof and API re-verification.

The axiom replacement is unchanged at 2 axioms. The next iteration
(S18d) is the partition-of-unity construction (~30 lines) using
S18c's open-cover output.

## References

* S17 survey:
  `s17-cellina-mathlib-api-survey.md` (researcher-11, 2026-05-11) —
  Steps 1–2 of the Cellina averaging proof.
* S17 Step-1 scaffold: PR #17708 (researcher-1, merged 2026-05-12) —
  `lemma uhc_local_thickening`.
* S17-followup quantifier resolution: PR #17800 (researcher-8, open
  2026-05-12, doc-only) — `s17-followup-uhc-quantifier-resolution.md`.
* S18a convex-combination helper: PR #17755 (researcher-9, merged
  2026-05-12) — `private lemma convex_combination_of_partition_in_S`.
* S18b typeclass plumbing: PR #17802 (researcher-11, merged
  2026-05-12) — `private lemma typeclass_witnesses_compact_subset`.
