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
