# S17 — Mathlib API Survey for `approx_selection_exists` Axiom Elimination

**Author**: researcher-11, 2026-05-11
**Iteration**: S17
**Mode**: BUILD (groundwork — no Lean code modified, no axioms eliminated this session)
**File**: `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`
**Target axiom**: `approx_selection_exists` (Cellina–Browder graph form, line 465)
**Mathlib pinned rev**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (≈ v4.26.0)

## Why this document

After **S16** (PR #17697) closed the docstring-vs-code drift, the file is end-to-end sorry-free with exactly two axioms:

1. `brouwer_unit_ball` — Brouwer FPT on closed unit ball. **Mathlib lacks this entirely** (S10 finding); replacing it would require an in-house Brouwer formalization (very large, multi-month).
2. `approx_selection_exists` — Cellina–Browder graph-approximate selection theorem. **Mathlib has all the underlying API**, so replacement is a focused (~200–500 Lean lines) Cellina averaging argument.

This document maps each step of the textbook Cellina proof (as written in the docstring at lines 437–462 of `SchauderFixedPointOQ03OQ01.lean`) to a precise Mathlib v4.26 lemma name. **Every lookup below was verified via the GitHub Contents API at the pinned rev** using the S10 methodology (`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0`), which is the only reliable surface for this worktree (the on-disk `proofs/.lake` self-symlink trap blocks local Mathlib browsing — see `feedback_researcher_lake_symlink_broken.md`).

The next implementation iteration (S18+) can land the proof against this exact API surface without re-doing the survey work.

## Setup recap (constraints under which we operate)

- Ambient space: `EuclideanSpace ℝ (Fin n)` — finite-dimensional real inner-product space, hence `PseudoMetricSpace` and `NormedAddCommGroup`.
- `S : Set (EuclideanSpace ℝ (Fin n))` with `S.Nonempty`, `IsCompact S`, `Convex ℝ S`.
- `↥S : Type` is the subtype, inheriting `PseudoMetricSpace` (and thus `T4Space`) from the ambient.
- `IsCompact S → CompactSpace ↥S` via `isCompact_iff_compactSpace.mp`.
- `F : SetValuedMap (↥S) (↥S)`, `IsUpperHemicontinuous F`, `∀ x, (F x).Nonempty`, `∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n)))`.
- Output: for any `ε > 0`, `∃ f : ↥S → ↥S, Continuous f ∧ IsGraphApproxSelection F (fun x => f x) ε`.

## Cellina averaging proof — step-by-step API map

### Step 1: For each `x ∈ S`, pick `y_x ∈ F(x)` and use UHC to get an open `U_x ∋ x` with `F(U_x) ⊆ ε`-thickening of `F(x)`.

| Sub-step | Mathlib name | Module | Notes |
|---|---|---|---|
| Pick `y_x ∈ F(x)` | `Set.Nonempty.choose` (or `Classical.choose` on `hF_ne x`) | `Mathlib.Data.Set.Basic` | Gives `y_x : ↥S`. |
| Open ε-thickening of `F(x)` in ambient `EuclideanSpace ℝ (Fin n)` | `Metric.thickening (ε) ((Subtype.val '' F x))` | `Mathlib.Topology.MetricSpace.Thickening` | Defined at line 53; `isOpen_thickening` at line 77. Use ambient image because `IsUpperHemicontinuous` is stated over open supersets in the codomain. |
| Open neighborhood `U_x ∋ x` (in `↥S`) with `F(U_x) ⊆ thickening` | Direct application of `IsUpperHemicontinuous F` (defined locally at line 69) on the open thickening | `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` line 69 | Need to verify the local `IsUpperHemicontinuous` definition takes ambient-image open sets, OR adjust to subtype-relative open sets. **Action item for S18**: read lines 69–89 carefully to confirm the `V` quantifier signature. |

**Risk**: The local `IsUpperHemicontinuous` definition may require `V : Set (↥S)` rather than `V : Set (EuclideanSpace ℝ (Fin n))`. If so, we need an extra step pulling the ambient thickening's preimage under `Subtype.val` to get a subtype-open set.

### Step 2: Compactness extracts a finite subcover `U_{x_1}, …, U_{x_k}`.

| Sub-step | Mathlib name | Module | Notes |
|---|---|---|---|
| Open cover from `{U_x : x ∈ ↥S}` | constructive — express as `⋃ x : ↥S, U_x` | n/a | Trivial. |
| Finite subcover from compactness of `↥S` | `IsCompact.elim_finite_subcover` | `Mathlib.Topology.Compactness.Compact` | Standard. Returns `Finset (↥S)` indexing the subcover. |

**Output**: `s : Finset (↥S)` with `(↥S : Set _) ⊆ ⋃ i ∈ s, U_i` (where `U_i := U_{x_i}`).

### Step 3: Subordinate partition of unity `{φ_i}` with `supp φ_i ⊆ U_{x_i}`.

This is the load-bearing step. Mathlib v4.26 provides:

| Mathlib name | Module | Signature | Hypothesis fit |
|---|---|---|---|
| `PartitionOfUnity.exists_isSubordinate` | `Mathlib.Topology.PartitionOfUnity` line 433 | `[NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) : ∃ ρ : PartitionOfUnity ι X s, ρ.IsSubordinate U` | We need `↥S` to be `NormalSpace` and `ParacompactSpace`. ✓ See instances below. |

Required typeclass instances on `↥S` (all available in Mathlib v4.26):

| Instance | Source | Mathlib name |
|---|---|---|
| `[ParacompactSpace ↥S]` | `↥S` is a metric space (`PseudoEMetricSpace`) | `instParacompactSpace` (`Mathlib.Topology.EMetricSpace.Paracompact` line 42) |
| `[NormalSpace ↥S]` (= T4 ⇒ T2 + Normal) | `↥S` is a metric space (`EMetricSpace`) | `t4Space` (`Mathlib.Topology.EMetricSpace.Paracompact` line 166) |
| `[CompactSpace ↥S]` | `IsCompact S` | `isCompact_iff_compactSpace.mp` |

Or alternatively, use compact ⇒ paracompact directly:
- `paracompact_of_compact [CompactSpace X] : ParacompactSpace X` (`Mathlib.Topology.Compactness.Paracompact` line 180).

After `exists_isSubordinate`, we get:
- `ρ : PartitionOfUnity (↥S) (↥S) Set.univ` (or restricted to `s : Finset (↥S)` via finite reindexing — depending on whether we use the Finset-indexed cover from step 2 or pass to `Subtype.val ∘ ...`)
- `ρ.IsSubordinate U` ⇒ `∀ i, tsupport (ρ i) ⊆ U_i`

### Step 4: Define `f(x) := ∑ φ_i(x) · y_{x_i}`. Convexity of `S` gives `f x ∈ S`.

This requires care: `y_{x_i} : ↥S`, but `∑ φ_i(x) · y_{x_i}` is a convex combination in the **ambient** `EuclideanSpace ℝ (Fin n)`. Convexity of `S` then puts the result back in `S`, and we lift to `↥S` via the subtype constructor.

| Sub-step | Mathlib name | Module | Notes |
|---|---|---|---|
| Convex combination is in `S` | `Convex.sum_mem` | `Mathlib.Analysis.Convex.Combination` line 212 | Signature: `(hs : Convex R s) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hz : ∀ i ∈ t, z i ∈ s) : ∑ i ∈ t, w i • z i ∈ s`. **Direct fit**. |
| `∑ φ_i(x) = 1` for `x ∈ S` | `PartitionOfUnity.sum_finsupport` | `Mathlib.Topology.PartitionOfUnity` line 198 | When using `s = univ`, all of `↥S` qualifies. |
| `0 ≤ φ_i(x)` | `PartitionOfUnity.nonneg` | `Mathlib.Topology.PartitionOfUnity` line 155 | Direct. |

**Continuity of `f`**: use `PartitionOfUnity.IsSubordinate.continuous_finsum_smul` (`Mathlib.Topology.PartitionOfUnity` line 313).

```
theorem IsSubordinate.continuous_finsum_smul [ContinuousAdd E] {U : ι → Set X}
    (hs : f.IsSubordinate U) {g : ι → X → E} (hg : ∀ i, ∀ x ∈ U i, ContinuousAt (g i) x) :
    Continuous fun x => ∑ᶠ i, f i x • g i x
```

For our case, `g i := fun _ => y_{x_i}` is constant (hence continuous everywhere), so `hg` is trivial.

### Step 5: Graph bound — at any `x`, pick `i` with `φ_i(x) > 0`; then `x ∈ U_{x_i}` ⇒ certify graph-distance `< ε`.

| Sub-step | Mathlib name | Module | Notes |
|---|---|---|---|
| `∃ i, 0 < ρ i x` for `x ∈ S` | `PartitionOfUnity.exists_pos` | `Mathlib.Topology.PartitionOfUnity` line 163 | Direct. |
| `0 < ρ i x ⇒ x ∈ tsupport (ρ i) ⊆ U_i` | `subset_tsupport` + `IsSubordinate` chase | n/a | Routine `Set.mem_of_mem_of_subset` chain. |
| `(x_i, y_{x_i}) ∈ graph(F)` | by construction (`y_{x_i} ∈ F(x_i)`) | n/a | Trivial. |
| Graph distance bound: `dist x x_i < ε` and `dist (f x) y_{x_i} < ε` | combination of `x ∈ U_i ⊆ Metric.ball x_i ε` (need to choose `U_x_i ⊆ Metric.ball x_i ε` in step 1) and the convex-combination centered-on-`y_{x_i}` argument | n/a | The radius choice in step 1 must be `min(ε, UHC-witness-radius)` to make this work. The actual `IsGraphApproxSelection` predicate (line 432 of the .lean file) requires `dist x x' < ε ∧ y ∈ F x' ∧ dist (f x) y < ε`; we exhibit `x' := x_i` and `y := y_{x_i}` (which lies in `F x_i`). |

**Subtle point**: the `dist (f x) y_{x_i} < ε` bound is the load-bearing convex-combination geometry. `f x` is a convex combination of `{y_{x_j}}` over indices `j` with `φ_j(x) > 0`; for all such `j`, `x ∈ U_{x_j}`, so by UHC `y_{x_j} ∈ ε`-thickening of `F(x_j)`. This does NOT directly give `dist (f x) y_{x_i} < ε` — it gives `dist (f x) (some point in F(x_j)) < ε` for each `j`. The graph form succeeds because we have the freedom to pick `x' = x_j` for any `j` (not necessarily `i`); the standard trick is to pick `x' := x_{j_0}` where `j_0` realizes the `φ`-positive index closest to `x`.

**Action item for S18**: re-derive the precise `2ε` vs `ε` constants used in step 5; the docstring at line 462 hints "passes a `2ε`-bound through `approx_fixedpoint_implies_fixedpoint`", suggesting the natural argument gives `2ε` and the axiom is invoked at `ε/2` to recover the literal `ε` bound. **Recommendation**: implement `approx_selection_exists` at the relaxed `2ε` bound (call it `approx_selection_exists_2eps`) first, then derive the literal `ε` form by halving — this matches what the kakutani caller already expects.

## Recommended S18 implementation order

1. **S18a (warm-up, ~30 lines)**: Add a private helper lemma `convex_combination_of_partition_in_S` packaging `Convex.sum_mem` together with `PartitionOfUnity.sum_finsupport` and `nonneg`. Provable now from Mathlib without partition-of-unity construction. Lands as a standalone PR; verifies the `Convex.sum_mem` API signature concretely under our use site.

2. **S18b (core ~80 lines)**: Add the typeclass instance plumbing: `[CompactSpace ↥S]`, `[ParacompactSpace ↥S]`, `[NormalSpace ↥S]` derivations as local `have` blocks at the start of the eventual `approx_selection_exists_proof` theorem. Land as a standalone PR (no axiom replacement yet).

3. **S18c (step 1 + 2, ~50 lines)**: Build the open cover `U_x` and extract finite subcover. Land as a standalone PR.

4. **S18d (step 3, ~30 lines)**: Invoke `PartitionOfUnity.exists_isSubordinate` against the finite subcover. Land as a standalone PR.

5. **S18e (step 4, ~40 lines)**: Define `f` via `PartitionOfUnity.IsSubordinate.continuous_finsum_smul` and verify `f x ∈ S` via `Convex.sum_mem`. Land as a standalone PR.

6. **S18f (step 5, ~50 lines)**: Graph-distance bound — the only mathematically delicate step (the `2ε`-vs-`ε` accounting from the docstring). Land as a standalone PR.

7. **S19 (axiom replacement, ~5 lines)**: Replace `axiom approx_selection_exists` with `theorem approx_selection_exists := approx_selection_exists_proof` once all S18a–f land. Sync `meta.json`: `axiomCount: 2 → 1`.

This decomposition keeps each PR small (≤80 lines), independent of the prior PR's build verification, and avoids the multi-hour Docker rebuild risk of a single 200–500-line monolith.

## Quick verification commands (for next session)

```bash
# Confirm pinned rev still applies
grep '"name": "mathlib"' proofs/lake-manifest.json -A1

# Re-fetch any Mathlib file at pinned rev
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Topology/PartitionOfUnity.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" --jq '.content' | base64 -d | less

# List existing axioms in our file
grep -nE "^axiom " proofs/Proofs/SchauderFixedPointOQ03OQ01.lean

# Confirm sorry-free
grep -cE "(^|[^a-zA-Z_])sorry($|[^a-zA-Z_])" proofs/Proofs/SchauderFixedPointOQ03OQ01.lean   # docstring "sorry" mentions persist; comment-strip is the truth
```

## Honest scope statement

**This document does not eliminate any axiom.** It is groundwork for the S18+ implementation. The deliverable is:

- A precise Mathlib v4.26 API map (every lemma name verified via GitHub Contents API at the pinned rev)
- A 6-PR decomposition that keeps each step ≤ 80 lines
- One identified action item (`IsUpperHemicontinuous` signature confirmation in step 1)
- One identified mathematical subtlety (the `2ε`-vs-`ε` accounting in step 5)

**Why this is real progress**: the previous "next action" in `state.md` (S11.B implementation) had been stale since S14 landed it (PR #17601). After S16 fixed the docstring drift, no document existed laying out the next concrete next-action surface. Without this survey, the natural failure mode is for the next claim cycle to re-read `s11-strict-weakening-spec.md` and rediscover that S11.B is done — wasting a full session. With this survey, S18a can be picked up directly.

## References

- **Cellina, A.** (1969) *Approximation of set valued functions and fixed point theorems*. Ann. Mat. Pura Appl. 82, 17–24.
- **Browder, F.** (1968) *The fixed point theory of multi-valued mappings in topological vector spaces*. Math. Ann. 177, 283–301.
- **Aubin, J.-P. & Frankowska, H.** (1990) *Set-Valued Analysis*. Birkhäuser. §9.2 (graph approximate selections).
- **Repovš, D. & Semenov, P. V.** (1998) *Continuous Selections of Multivalued Mappings*. Kluwer. §3.2 (selection theory hierarchy).
