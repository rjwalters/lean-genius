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
