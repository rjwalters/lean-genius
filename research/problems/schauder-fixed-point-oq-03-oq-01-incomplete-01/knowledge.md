# Knowledge Base: schauder-fixed-point-oq-03-oq-01-incomplete-01

Insights accumulated during research on this problem.

---

## Problem Understanding

The file SchauderFixedPointOQ03OQ01.lean derives Kakutani's fixed point theorem
from Brouwer's via Cellina's approximate continuous selections + a metric-space
limit argument. Two sorries existed pre-S3:
- `kakutani_from_brouwer` (combination argument)
- `approx_fixedpoint_implies_fixedpoint` (limit argument helper)

Three axioms were declared (Brouwer FPT, approximate selection existence,
sequential compactness).

---

## Insights

### S2 (researcher-3, 2026-05-07)
- Identified that closing `approx_fixedpoint_implies_fixedpoint` also closes
  `kakutani_from_brouwer` via a clean reduction.
- Documented a 4-step proof outline for the helper.
- Build verification deferred due to memory pressure.

### S3 (researcher-11, 2026-05-08)

#### Pre-existing compilation bug
The `Convex ℝ (F x)` clause (in both the `approx_selection_exists` axiom and
the `kakutani_from_brouwer` theorem signature) was malformed: `F x : Set ↥S`
where `↥S` lacks `AddCommMonoid`. Lean elaborated this as a `sorry` placeholder.
The S2 PR (#16731) was docstring-only and was merged without an actual build,
so this masked compilation failure went unnoticed. Fix: lift via
`Subtype.val '' F x : Set (EuclideanSpace ℝ (Fin n))`, which is well-typed.

#### Axiom elimination
`seq_compact_of_compact` was an axiom but is just a one-line consequence of
Mathlib's `IsCompact.isSeqCompact` for `PseudoMetricSpace`. Now a theorem.
Axiom count: 3 → 2.

#### Helper proof
`approx_fixedpoint_implies_fixedpoint` proved using:
- `choose` to extract sequences from `happrox`
- `seq_compact_of_compact` for subsequence
- `squeeze_zero` + `tendsto_one_div_add_atTop_nhds_zero_nat` for `dist→0`
- `tendsto_iff_dist_tendsto_zero` + `dist_triangle` for `yseq→x_star`
- `by_contra` + case split on `(F x*).Nonempty`
- Nonempty case: union-of-balls `V := ⋃ y ∈ F x*, Metric.ball y (δ/2)` as the
  open neighborhood (instead of `Metric.thickening` to avoid EMetric API
  uncertainty), then UHC + triangle inequality with `Metric.infDist_le_dist_of_mem`.
- Empty case: `V := ∅` directly via UHC.

#### Kakutani proof body
~25 lines: chains `approx_selection_exists` + `brouwer_fpt` +
`approx_fixedpoint_implies_fixedpoint` via the subtype-univ trick
(`isCompact_iff_compactSpace.mp` + `isCompact_univ`).

#### Build verification deferred
Docker Desktop caps each container at ~7.65GiB regardless of `LEAN_MEMORY_LIMIT`;
with 8+ concurrent agents, my build OOM'd at 510s during the Mathlib clone phase.
Code structure-checked and lemma names cross-referenced against gallery usage
but not Lean-compiled. Marked as build-pending in PR.

### S8 (researcher-4, 2026-05-08)

#### `brouwer_fpt` reduction to closed-ball Brouwer + retraction
Documented the second axiom-elimination path in
`s8-brouwer-extension-via-projection.md`. The construction:

- `S` compact convex nonempty in `EuclideanSpace ℝ (Fin n)` ⇒ `S` bounded ⇒
  `S ⊆ Metric.closedBall 0 R` for some `R > 0` (`IsCompact.isBounded` +
  `Bornology.IsBounded.exists_pos_subset_closedBall`).
- Strict convexity of the Euclidean norm gives a unique nearest-point
  projection `r : E → ↥S` (continuous, identity on `↥S`) — folklore from
  Smart 1980 §1.3, Granas–Dugundji 2003 §0.4 Thm 4.6, packaged in Mathlib via
  the `Convex.exists_unique_dist_eq` family near
  `Mathlib.Analysis.InnerProductSpace.Convex` /
  `Mathlib.Analysis.Convex.SpecificFunctions.Basic`.
- Given `f : ↥S → ↥S`, factor through `B := closedBall 0 R`:
  `F : ↥B → ↥B, F b := ⟨↑(f (r b)), …⟩`; this is well-defined because
  `f (r b) ∈ ↥S ⊆ B`, and continuous as a composition.
- Closed-ball Brouwer (Mathlib's unit-ball form, rescaled by `Homeomorph.smul`
  if Mathlib only has the unit ball directly) gives `F b₀ = b₀`; from
  `F b₀ = ↑(f (r b₀)) ∈ S` we get `b₀ ∈ S`, then `r b₀ = b₀` by idempotency,
  then `f b₀ = b₀`.

#### Lean stub with three `LOOKUP-N` sorries
Wrote a complete Lean proof skeleton in the analysis note (not in
`SchauderFixedPointOQ03OQ01.lean`; this iteration is analysis-only following
the S6→S7 pattern). Three localized sorries:

- **LOOKUP-1**: bounded set fits in a closed ball.
- **LOOKUP-2**: continuous nearest-point projection onto closed convex set.
- **LOOKUP-3**: closed-ball Brouwer at general radius.

Each is a single Mathlib API call; S9 only needs to resolve names, not design
proofs.

#### Strict-convexity dependency
The retraction construction *requires* strict convexity of the ambient norm
(otherwise nearest-point projection is multi-valued). For
`EuclideanSpace ℝ (Fin n)` this is automatic
(`InnerProductSpace.toStrictConvexSpace` or
`EuclideanSpace.instStrictConvexSpace`). Worth flagging because the
`SetValuedMap` framework in this file naturally extends to multi-valued
projections in non-strictly-convex spaces; a future variant for `ℓ¹`/`ℓ∞`
would need the Cellina–Browder graph form for the projection too.

---

## Dead Ends

- `Metric.thickening`: avoided due to EMetric/`ENNReal.ofReal` complications and
  uncertainty about exact lemma names (`mem_thickening_iff` vs
  `mem_thickening_iff_infDist_lt`). Replaced with explicit union-of-balls.
- `Metric.infDist_le_dist_add_infDist`: name in original docstring may be wrong
  (Mathlib has `infDist_le_infDist_add_dist` with reversed order); avoided by
  reformulating contradiction via `dist_triangle` + `infDist_le_dist_of_mem`.
- `simp_rw [dist_comm]`: would loop because `dist_comm a b = dist b a` rewrites
  in both directions. Replaced with `simpa [dist_comm] using h`.

---

## S10 (researcher-12, 2026-05-08)

### LOOKUP-3 resolved against pinned mathlib4 rev — definitively absent

Direct GitHub-API inspection of mathlib4 at the pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the rev recorded in
`proofs/lake-manifest.json` for `inputRev: "v4.26.0"`) settles S9's
flagged scenario question:

- `docs/100.yaml` Brouwer entry's only `result:` link is the external
  Lean 3 repo `Shamrock-Frost/BrouwerFixedPoint`.
- `docs/1000.yaml` Brouwer entry is annotated `comment: "in Lean 3"`
  (the Mathlib-curator convention for unported theorems).
- A repo-wide GitHub code search for `Brouwer language:lean` in
  `leanprover-community/mathlib4` returns three files only:
  `Mathlib/Order/Heyting/Basic.lean`,
  `Mathlib/Order/CompleteBooleanAlgebra.lean`,
  `Mathlib/Order/PrimeSeparator.lean`. All three reference the
  *order-theoretic / lattice* Brouwer (Brouwer–Heyting–Kolmogorov), not
  the topological FPT.
- `Mathlib/Topology/MetricSpace/` has no `Brouwer.lean` file at the
  pinned rev (47 files, all listed in the S10 note).
- The same searches against the current default branch return identical
  results, ruling out a recent landing.

**Conclusion:** Mathlib4 lacks Brouwer FPT entirely — neither the
general compact-convex form nor the unit-ball form. The S8 docstring
claim that it is "proved in Mathlib for the unit ball via degree
theory" was incorrect. This places LOOKUP-3 in S9's *scenario 2*
(Mathlib-level block).

### Decision: Option A (strict-weakening) recommended for S11

Three options were evaluated in `s10-mathlib-v426-lookup3-resolved.md`:

| Option | Axiom count Δ | Axiom strength Δ | Lean lines | Sessions |
|---|---|---|---|---|
| A — strict-weakening (`brouwer_unit_ball` + retraction reduction) | 0 | reduced (general → unit ball) | ~60 | 1–2 |
| B — in-house Brouwer FPT proof (Sperner-based or degree-theoretic) | -1 | reduced to 0 | 500–1500 | 5–15 |
| C — status quo | 0 | unchanged | 0 | 0 |

Option A is the recommended next iteration because:
1. It produces verifiable Lean progress in a single session.
2. The retraction reduction needed for Option A is the same shape as
   S8's Lean stub, so the work is largely already designed.
3. The LOOKUP-2 work (continuous nearest-point projection helper, S9
   §"Updated estimate") is required by either Option A or Option B and
   so is not duplicated.
4. Option B remains a future upgrade path that does not contradict
   Option A — the new `axiom brouwer_unit_ball` is a clean target for a
   later in-house proof.

### Why this iteration matters

S9 left LOOKUP-3 as the single open question gating the brouwer_fpt
elimination, with the explicit ask "the next session should resolve
scenario 1 vs 2 first, before touching any Lean." S10 does exactly
that. The implementation iteration (S11.A + S11.B) can now proceed with
no remaining design uncertainty on the Brouwer side; the only
unresolved sub-task is the LOOKUP-2 helper's continuity proof, which
S9 already scoped (~50 lines, variational-inequality method).

### Methodology note (reusable)

When `proofs/.lake` is broken and the on-disk Mathlib copy is at the
wrong toolchain version, lookup of names against a pinned mathlib rev
is still tractable via the GitHub API:

```bash
REV=$(jq -r '.packages[] | select(.name=="mathlib") | .rev' \
  proofs/lake-manifest.json)

# List a specific folder at the pinned rev
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Some/Folder?ref=$REV" \
  --jq '.[].name'

# Read a specific file at the pinned rev
gh api "repos/leanprover-community/mathlib4/contents/path/to/file.lean?ref=$REV" \
  | jq -r '.content' | base64 -d | head -50

# Repo-wide code search (NOTE: not pinnable to a rev; use only for absence
# tests across master/default-branch and the pinned rev jointly)
gh api -X GET "search/code?q=<query>+language:lean+repo:leanprover-community/mathlib4" \
  --jq '.items[].path'
```

Absence findings via the pinned-`?ref=$REV` content API are
authoritative for the build's actual mathlib version, unlike grep
against a divergent on-disk copy.

### S18b (researcher-11, 2026-05-12, this iteration)

**Four-typeclass derivation chain on `↥S` is one `haveI` away.** For
`S : Set (EuclideanSpace ℝ (Fin n))` with `IsCompact S`, the eventual
`approx_selection_exists_proof` (S18c–f) needs four typeclass instances
on `↥S`: `CompactSpace`, `T2Space`, `NormalSpace`, `ParacompactSpace`.
Verified at pinned Mathlib v4.26.0 rev `2df2f0150c…`:

- `CompactSpace ↥S` — explicit `haveI` via
  `isCompact_iff_compactSpace.mp hS_compact`
  (`Mathlib/Topology/Compactness/Compact.lean` L989).
- `T2Space ↥S` — auto from `Subtype.t2Space`
  (`Mathlib/Topology/Separation/Hausdorff.lean` L351); ambient
  `EuclideanSpace ℝ (Fin n)` is `T2Space` via its metric structure.
- `R1Space ↥S` — auto from `T2Space.r1Space`
  (`.../Hausdorff.lean` L120).
- `NormalSpace ↥S` — auto from `NormalSpace.of_compactSpace_r1Space`
  (`Mathlib/Topology/Separation/Regular.lean` L489), now available
  because `[CompactSpace ↥S]` and `[R1Space ↥S]` are in scope.
- `ParacompactSpace ↥S` — auto from `paracompact_of_compact`
  (`Mathlib/Topology/Compactness/Paracompact.lean` L180).

The `private lemma typeclass_witnesses_compact_subset` is the safety
check: it confirms the four-typeclass chain succeeds, isolating any
future Mathlib API drift to a single typecheck site.

**`IsUpperHemicontinuous` quantifies over subtype-relative open sets**
(line 71 of the file: `∀ V : Set Y, IsOpen V → IsOpen {x | F x ⊆ V}`;
`IsOpen V` resolved in `Y`'s topology). When `Y := ↥S`, the topology
on `Y` is the subtype topology, so `V` ranges over subtype-relative
opens. Therefore S17's `uhc_local_thickening` (PR #17708) is
**directly applicable** in S18c — no preimage-pull step needed.
Resolves the S17 survey's outstanding action item.

### S26 ACT (researcher-1, 2026-05-28)

Build-verified clean (3074 jobs, 45s file compile) under recovered INFRA
(Docker v29.4.1, host disk 68 Gi free — the S22–S25 blockers G7/G8 are
gone). 0 functional sorries, 2 axioms unchanged.

**Input-ball clause now propagated through the selection bundle.** The
S18f helper `uhc_local_thickening_with_input_diameter` (PR #18257) had
sharpened S17's `uhc_local_thickening` with the input-side bound
`U x₀ ⊆ Metric.ball x₀ ε`, but it was never threaded into the
`exists_finite_subcover_for_uhc` → `exists_partition_subordinate_to_uhc_cover`
→ `exists_continuous_selection_with_witnesses` chain (S18c–e all still
called the weaker S17 helper). This iteration switches S18c to the S18f
helper and adds the clause `(∀ x, U x ⊆ Metric.ball x ε)` to all three
result bundles. This is the "propagated through the S18d/S18e packaging
in a subsequent iteration" step explicitly deferred by the S18f note.

**`dist x x' < ε` half of the graph bound is now a lemma.** New
`private lemma finsupport_center_within_input_ball`: for any `x` and any
`i ∈ ρ.finsupport x`, `dist x i < ε`. Proof: `mem_finsupport` ⟹
`ρ i x ≠ 0` ⟹ `x ∈ support (ρ i)` ⟹ (`subset_tsupport`) `x ∈ tsupport (ρ i)`
⟹ (`ρ.IsSubordinate U`) `x ∈ U i` ⟹ (input-ball clause) `x ∈ ball i ε`.
With witness `x' := i`, this discharges the first of the three
`IsGraphApproxSelection` conjuncts; `y := ysel i ∈ F i` discharges the
second.

**Directional gap in the output-side bound (corrects the S18e plan).**
The S18e docstring sketched closing `dist (f x) (ysel i) < ε` via
"`ysel i ∈ F i ⊆ ε-thickening of F x`". That direction is **not**
available: the thickening clause is `z ∈ U x ⟹ F z ⊆ thickening ε (F x)`,
so `x ∈ U i` yields `F x ⊆ thickening ε (F i)` — it bounds `F x`, not the
selected values `ysel j ∈ F j` (`j ∈ ρ.finsupport x`), and gives no
control of `ysel j` relative to `ysel i`/`F i`. Closing the output half
needs a *uniform* refinement (Lebesgue-number style: ensure all centers
`x_j` with `ρ j x > 0` lie in a single neighborhood on which `F` is
`ε`-thickening-controlled, then average), not a mechanical chaining of
the current helpers. This is the genuine remaining obstacle for the
axiom elimination; the convexity hypothesis `hF_convex` plus the S22
nearest-point helper `exists_nearest_in_image_F` are the natural tools
once the uniform bound is in place.
