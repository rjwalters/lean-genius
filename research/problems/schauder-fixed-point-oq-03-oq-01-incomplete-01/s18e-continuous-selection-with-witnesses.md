# S18e — Continuous Selection from Subordinate Partition of Unity

**Iteration**: S18e
**Author**: researcher-11
**Date**: 2026-05-12
**PR**: (this iteration)
**File**: `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`
**Net change**: lineCount 1015 → 1119 (+104); theoremCount 10 → 11 (+1);
sorry count 0 → 0; axiom count 2 → 2.

## Goal

Package Step 4 of the Cellina–Browder construction
(`approx_selection_exists` axiom elimination) as a private helper lemma
suitable for direct consumption by the eventual S18f graph-bound
proof. Step 4 defines the candidate continuous selection
`f : C(↥S, ↥S)` from the S18d subordinate partition of unity
(PR #17993).

## Lemma signature

```
private lemma exists_continuous_selection_with_witnesses {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty) (hF_uhc : IsUpperHemicontinuous F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : C(↥S, ↥S),
      ∃ U : ↥S → Set ↥S,
      ∃ ρ : PartitionOfUnity (↥S) (↥S) (Set.univ : Set ↥S),
      ∃ ysel : ↥S → ↥S,
        (∀ x : ↥S, IsOpen (U x)) ∧
        (∀ x : ↥S, x ∈ U x) ∧
        (∀ x z : ↥S, z ∈ U x → F z ⊆ Metric.thickening ε (F x)) ∧
        ρ.IsSubordinate U ∧
        (∀ x, ysel x ∈ F x) ∧
        (∀ x : ↥S, (f x : EuclideanSpace ℝ (Fin n))
            = ∑ᶠ i, ρ i x • (ysel i : EuclideanSpace ℝ (Fin n)))
```

The full witness bundle is intentionally exposed so that S18f can
read off any datum it needs without re-running S18a–d.

## Proof structure

1. **`choose ysel hysel_in_F using hF_ne`** — selects one
   `ysel x ∈ F x` per `x : ↥S` (axiom of choice; the selector
   need not be continuous — continuity comes from averaging).
2. **S18d unpacking** — `exists_partition_subordinate_to_uhc_cover`
   yields `U, ρ, hU_open, hU_mem, hU_sub, hρ_sub`.
3. **Continuity of f0**:
   ```
   f0 : ↥S → EuclideanSpace ℝ (Fin n) :=
     fun x => ∑ᶠ i, ρ i x • (ysel i : EuclideanSpace ℝ (Fin n))
   ```
   from `PartitionOfUnity.IsSubordinate.continuous_finsum_smul`
   applied to the constant-in-`x` family
   `g i _ := (ysel i : EuclideanSpace ℝ (Fin n))` with
   `ContinuousOn (g i) (U i) = continuousOn_const`.
4. **Membership f0 x ∈ S** via `convex_combination_of_partition_in_S`
   (S18a, PR #17755) at `K = S`, using `(ysel i).property` for the
   point-in-S hypothesis and `ρ.sum_finsupport_smul_eq_finsum` to
   bridge the finsum form to the `Finset`-sum form expected by the
   helper.
5. **Lift to f : C(↥S, ↥S)** via `Continuous.subtype_mk`
   (`Mathlib.Topology.Constructions` line 399 at pinned rev).
6. **Witness bundle** — `refine ⟨…, ?_⟩` then `intro _; rfl` (the
   formula clause is definitional because `f` is built directly from
   `f0`).

## Mathlib API references (verified at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| Symbol | File | Line |
|--------|------|------|
| `PartitionOfUnity.IsSubordinate.continuous_finsum_smul` | `Mathlib/Topology/PartitionOfUnity.lean` | 313 |
| `PartitionOfUnity.sum_finsupport_smul_eq_finsum` | `Mathlib/Topology/PartitionOfUnity.lean` | 212 |
| `Continuous.subtype_mk` | `Mathlib/Topology/Constructions.lean` | 399 |
| `continuousOn_const` | `Mathlib/Topology/ContinuousOn.lean` | 717 |

The S18a helper `convex_combination_of_partition_in_S` (PR #17755) and
the S18d helper `exists_partition_subordinate_to_uhc_cover` (PR
#17993) are in-file dependencies.

## Build status

**Build pending — S18e new lemma isolates cleanly; parent drift
unrelated.**

Local Docker build (`./proofs/scripts/docker-build.sh
Proofs.SchauderFixedPointOQ03OQ01`) reports two errors, BOTH in the
pre-existing `lemma exists_continuous_proj_convex` (lines 167–250 of
the file), unrelated to S18e:

```
error: Proofs/SchauderFixedPointOQ03OQ01.lean:171:71: unsolved goals
case hVI ...
error: Proofs/SchauderFixedPointOQ03OQ01.lean:191:15: expected token
```

The `Mathlib.Analysis.InnerProductSpace.Projection` module was
deprecated since the S15 drift fix (PR #17654, 2026-05-09); the
deprecation cascade broke the `⟪…, …⟫_ℝ` inner-product notation at
line 191 and the `norm_eq_iInf_iff_real_inner_le_zero` symbol used at
line 194 in the existing `exists_continuous_proj_convex` helper.

No errors are reported at lines 711+ (the S18e lemma range); the
`info:` messages at lines 1112–1117 are pre-existing `#check`
emissions for the file's public surface (`brouwer_unit_ball`,
`brouwer_fpt`, `exists_continuous_proj_convex`, `approx_selection_exists`,
`approx_fixedpoint_implies_fixedpoint`, `kakutani_from_brouwer`) that
the elaborator continued to emit despite the earlier errors.

Build log: `.loom/logs/researcher-11-schauder-s18e-build.log`.

## Next step

S18f: discharge `axiom approx_selection_exists` by deriving
`IsGraphApproxSelection F (fun x => (f x : ↥S)) ε` from the witness
bundle returned by `exists_continuous_selection_with_witnesses`. At
any `x : ↥S`, pick any `i ∈ ρ.finsupport x` (nonempty because
`∑ ρ i x = 1`); extract `x ∈ U i` from
`tsupport (ρ i) ⊆ U i` (the `IsSubordinate` clause) and the strict
positivity `ρ i x > 0`. Then use
`hU_sub i x : F x ⊆ Metric.thickening ε (F i)` plus the chain
`ysel j ∈ F j` for every `j ∈ ρ.finsupport x` to bound
`dist (f x) (ysel i)` via the triangle inequality on the convex
combination defining `f x`.

Parent-drift fix (lines 171/191) is orthogonal to the S18 axiom
elimination work; can be addressed by a separate mechanic PR
swapping `Mathlib.Analysis.InnerProductSpace.Projection` for its
five replacement submodules (warning at line 45 of the build log
suggests the exact replacement).
