# Research State: schauder-fixed-point-oq-03-oq-01-incomplete-01

## Current State
**Phase**: ACT (S18c open-cover + finite subcover landed; **0 sorries**, 2 axioms remaining)
**Path**: full
**Since**: 2026-05-12T06:10:00Z
**Iteration**: 18c

## Current Focus
S18c (researcher-3, 2026-05-12, this iteration): Added `private lemma
exists_finite_subcover_for_uhc` packaging Cellina–Browder Steps 1–2 in
a single statement. For a compact `S ⊆ EuclideanSpace ℝ (Fin n)` and
an upper-hemicontinuous `F : ↥S → 2^↥S` at any `ε > 0`, the lemma
yields a function `U : ↥S → Set ↥S` of subtype-relative open
neighborhoods plus a finite `s : Finset ↥S` such that (i) each `U x`
is open in `↥S` and contains `x`, (ii) `F(U x) ⊆ ε`-thickening of
`F(x)` for every `x`, and (iii) the family `{U x : x ∈ s}` covers
`↥S` (`⋃ x ∈ s, U x = (⊤ : Set ↥S)`). Proof: `haveI [CompactSpace ↥S]`
from `isCompact_iff_compactSpace.mp` (the same line as S18b);
pointwise `choose` of `uhc_local_thickening` (S17 PR #17708) to
construct `U` with its three witnessing properties; then
`CompactSpace.elim_nhds_subcover U (fun x => (hU_open x).mem_nhds
(hU_mem x))` to extract the finite Finset. Net file change: lineCount
907 → 957 (+50); theoremCount 8 → 9 (+1); sorry count unchanged at 0;
axiom count unchanged at 2. Build pending (`proofs/.lake`
recursive-symlink trap forces ~45 min cold Docker clone; the two
Mathlib API references (`isCompact_iff_compactSpace` at
Compactness/Compact.lean L989 and `CompactSpace.elim_nhds_subcover` at
Compactness/Compact.lean L763) re-verified at pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via GitHub Contents API).

S18b (researcher-11, 2026-05-12, PR #17802 merged): Added `private lemma
typeclass_witnesses_compact_subset` confirming that the four typeclass
instances required for the Cellina–Browder construction
(`CompactSpace ↥S`, `T2Space ↥S`, `NormalSpace ↥S`, `ParacompactSpace ↥S`)
are derivable from `IsCompact S` alone at the pinned Mathlib v4.26.0
rev. Only `CompactSpace` requires an explicit `haveI`
(`isCompact_iff_compactSpace.mp hS_compact`); the remaining three are
auto-inferred from `Subtype.t2Space` (Separation/Hausdorff.lean L351),
`NormalSpace.of_compactSpace_r1Space` (Separation/Regular.lean L489;
`R1Space ↥S` chained from `T2Space.r1Space` at L120 of Hausdorff.lean),
and `paracompact_of_compact` (Compactness/Paracompact.lean L180). Net
file change: lineCount 864 → 907 (+43); theoremCount 7 → 8 (+1); sorry
count unchanged at 0; axiom count unchanged at 2. Also synced
meta.json drift from S17 #17708 and S18a #17755 (the meta values had
not been updated through the two intervening merges): top-level meta
+ leanFile both go from `lineCount=827, theoremCount=6, imports=7` to
`lineCount=907, theoremCount=8, imports=10`, plus three new
`originalContributions` entries for S17/S18a/S18b. Build pending
(`proofs/.lake` recursive-symlink trap forces ~45 min cold Docker
clone; all four Mathlib API references verified at pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via GitHub Contents API).

**Independent S18-prep finding (this iteration):** `IsUpperHemicontinuous`
at line 71 quantifies over `V : Set Y` with `IsOpen V` in the *ambient*
topology of `Y` — when applied to `F : SetValuedMap ↥S ↥S`, `Y = ↥S`
already carries the subtype topology, so `V` ranges over **subtype-relative**
open sets. This confirms that S17's `uhc_local_thickening` (PR #17708)
is directly applicable in the eventual `approx_selection_exists_proof`
without an extra preimage-pull step. (Resolved the action item from
s17 survey, step 1.)

S18a (researcher-9, 2026-05-12, PR #17755 merged): Added `private lemma
convex_combination_of_partition_in_S` packaging `Convex.sum_mem` with
`PartitionOfUnity.nonneg` and `PartitionOfUnity.sum_finsupport` into a
single one-line lemma for the Step-4 convex-combination membership check.
+48 lines (lineCount 779→827, theoremCount 5→6).

S17 (researcher-11, 2026-05-11, survey + plan): Mathlib v4.26 API survey
for `approx_selection_exists` (Cellina–Browder graph form) axiom
elimination. After S16 (PR #17697) closed the docstring-vs-code drift
that left the iter 13 next-action stale (S11.B was already done at S14),
no document existed mapping the next concrete axiom-elimination surface.
S17 maps every step of the textbook Cellina averaging proof (5 steps,
lines 437–462 of `SchauderFixedPointOQ03OQ01.lean`) to a precise Mathlib
v4.26 lemma name verified via GitHub Contents API at pinned rev
2df2f0150c. Net file change: **none** (no Lean code modified). Sorry
count 0; axiom count 2; lineCount 779. See
`s17-cellina-mathlib-api-survey.md` for the 6-PR decomposition plan
(S18a–f, each ≤ 80 lines).

S16 (researcher-8, 2026-05-12T00:19Z, PR #17697 merged): Docstring-only
synchronization. Removes 5 in-file references to `exists_continuous_proj_convex`
as "currently sorry-stubbed (S11.B work item)" and to `theorem brouwer_fpt`
as "not yet end-to-end sorry-free", which were stale narrative artifacts
from iter 13 surviving the S14/S15 implementation merges. Footer
"Path to Full Verification" → "Path to Axiom Elimination" with
`approx_selection_exists` (PartitionOfUnity + Cellina averaging) as
item 1, optional far-future in-house Brouwer as item 2. Net change:
sorry/axiom count unchanged at 0/2, lineCount 766 → 779.

S15 (researcher-3, 2026-05-09, PR #17654 merged): Mathlib API drift fix
on the S13/S14 elementwise-rescaling step in theorem brouwer_fpt.
4 sites: `Metric.mem_closedBall_zero_iff` → `mem_closedBall_zero_iff`
(root namespace, generated via `@[to_additive]` from `mem_closedBall_one_iff`
at Mathlib v4.26.0). Sorry count unchanged at 0; axiom count unchanged at 2.

S14 (researcher-3, 2026-05-09, PR #17601 merged): Fills the final
`sorry` on `lemma exists_continuous_proj_convex` (LOOKUP-2 helper)
with a complete proof using the Hilbert projection theorem
(`exists_norm_eq_iInf_of_complete_convex`) for existence, the
variational inequality (`norm_eq_iInf_iff_real_inner_le_zero`) for
continuity (1-Lipschitz from variational inequality + Cauchy–Schwarz),
and `ciInf_le` for idempotency. Net file change: sorry count 1 → **0**;
axiom count unchanged at 2; line count ~668 → ~766.

S13 (researcher-10, 2026-05-09, PR #17575 merged): Replaces the `sorry`
in `theorem brouwer_fpt`'s body with the ~140-line retraction
reduction proof per s11/s12 spec.

## Path to Axiom Elimination
The file is sorry-free; the only remaining work is axiom elimination.
Two axioms remain:

1. `axiom brouwer_unit_ball` (closed-unit-ball Brouwer FPT) — Mathlib
   v4.26 LACKS Brouwer FPT entirely (S10 finding). Replacement requires
   an in-house Brouwer formalization (very large, likely multi-month).
   **Out of scope for near-term iterations.**

2. `axiom approx_selection_exists` (Cellina–Browder graph form) —
   Mathlib v4.26 has all the underlying API. Replacement is ~200–500
   Lean lines. **In scope.** S17 mapped the API surface; S18a–f
   decomposes implementation into 6 PRs (each ≤ 80 lines).

## Next Action
**S18d (next claim, ~30 lines)**: Subordinate partition of unity
(Cellina Step 3). With S18c's `U : ↥S → Set ↥S` open family and the
typeclass instances from S18b (`[NormalSpace ↥S]`,
`[ParacompactSpace ↥S]`) in scope, invoke
`PartitionOfUnity.exists_isSubordinate`
(`Mathlib.Topology.PartitionOfUnity` L433) to obtain
`ρ : PartitionOfUnity (↥S) (↥S) Set.univ` with `ρ.IsSubordinate U`.
Package as `private lemma exists_partition_subordinate_to_uhc_cover`
threading the S18c output (`U` and `Set.univ ⊆ ⋃ x : ↥S, U x`,
obtained from `hU_mem x : x ∈ U x` via `Set.subset_iUnion`) into
`exists_isSubordinate`. The `hs : IsClosed s` hypothesis is
`isClosed_univ`. No axiom elimination yet; readies S18e (continuous
selection construction).

## Open PRs
- PR #17493 (researcher-5, 2026-05-08T22:43Z): S11 — closed-ball Brouwer
  specialization (very old, predates S11.A strict-weakening; superseded
  by current `axiom brouwer_unit_ball` form).
- PR #17708 (S17 Step-1 scaffold) MERGED 2026-05-12T03:21Z; no longer open.

## Iteration History (recent)

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S13 | 2026-05-09 | researcher-10 | #17575 (merged) | brouwer_fpt body filled (~140 lines); sorry 2→1 |
| S14 | 2026-05-09 | researcher-3 | #17601 (merged) | exists_continuous_proj_convex helper proven; sorry 1→0 |
| S15 | 2026-05-09 | researcher-3 | #17654 (merged) | Mathlib API drift fix |
| S16 | 2026-05-12 | researcher-8 | #17697 (merged) | docstring sync to actual sorry-free state |
| S17 | 2026-05-11 | researcher-11 | #17711 (merged) | Mathlib v4.26 API survey for `approx_selection_exists` axiom elimination |
| S17 | 2026-05-12 | researcher-1 | #17708 (merged) | `lemma uhc_local_thickening` Cellina–Browder Step-1 scaffold (+37 lines) |
| S18a | 2026-05-12 | researcher-9 | #17755 (merged) | Private helper `convex_combination_of_partition_in_S` (+48 lines) |
| S18b | 2026-05-12 | researcher-11 | #17802 (merged) | Private helper `typeclass_witnesses_compact_subset` (+43 lines, +1 theorem, meta sync 827→907) |
| S18c | 2026-05-12 | researcher-3 | (this PR) | Private helper `exists_finite_subcover_for_uhc` packaging Steps 1–2 (+50 lines, +1 theorem, meta sync 907→957) |

## Reference Files (in this directory)
- `problem.md` — original problem statement
- `knowledge.md` — accumulated knowledge log
- `s6-axiom-counterexample.md` — pointwise-selection counterexample (motivates the graph form)
- `s8-brouwer-extension-via-projection.md` — S8 (researcher-4) retraction sketch
- `s9-mathlib-lookup-refinements.md` — S9 (researcher-5) Mathlib reconnaissance
- `s10-mathlib-v426-lookup3-resolved.md` — S10 (researcher-12) GitHub-API resolution
- `s11-strict-weakening-spec.md` — S11 (researcher-5) strict-weakening lift spec
- `s11-brouwer-unit-ball-signature-refinement.md` — S11 signature refinement note
- `s12-s11a-body-step6-refinement.md` — S12 step-6 refinement
- `s13-s11a-body-implementation.md` — S13 (researcher-10) implementation note
- `s14-s11b-implementation.md` — S14 (researcher-3) helper implementation note
- `s15-mathlib-api-drift-fix.md` — S15 (researcher-3) drift-fix note
- `s17-cellina-mathlib-api-survey.md` — S17 (researcher-11) Mathlib API map for axiom elimination
- `s18a-convex-combination-helper.md` — S18a (researcher-9, merged #17755) convex-combination-of-partition-of-unity helper note
- `s18b-typeclass-witnesses.md` — S18b (researcher-11, merged #17802) typeclass instance plumbing note
- `s18c-open-cover-finite-subcover.md` — **S18c (this iteration)** open-cover + finite-subcover packaging note

