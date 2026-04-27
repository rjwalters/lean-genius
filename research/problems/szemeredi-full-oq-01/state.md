# Research State: szemeredi-full-oq-01

## Current State
**Phase**: ACT (specification mode under disk pressure)
**Path**: full
**Since**: 2026-04-23T03:54:35+02:00
**Iteration**: 4

## Current Focus

`FurstenbergCorrespondenceOQ01.lean` already contains 656 lines of fully proved Cesàro
infrastructure. The single remaining local axiom is:

```lean
axiom seqCompact_probabilityMeasure_cantor :
    ∀ (f : ℕ → ProbabilityMeasure CantorSpace),
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
    ∃ μ : ProbabilityMeasure CantorSpace,
    Filter.Tendsto (fun k => f (φ k)) Filter.atTop (nhds μ)
```

Plus ~30 lines of "density preservation at limit" for clopen B₀.

## Active Approach

Two-path Mathlib API plan (documented in knowledge.md Session 4):

- **Path A (recommended)**: Banach-Alaoglu + Riesz embedding. Use
  `WeakDual.isCompact_closedBall` + `IsCompact.image` to obtain `CompactSpace
  (ProbabilityMeasure CantorSpace)`, then apply `FirstCountableTopology.seq_compact_of_compact`.
- **Path B (alternative)**: direct Levy-Prokhorov metric completeness + total boundedness ⇒
  compact. Requires confirming Mathlib has `CompleteSpace (LevyProkhorov (ProbabilityMeasure
  CompactSpace))`.

## Attempt Count
- Total attempts: 4 (sessions 1-4)
- Current approach attempts: 4
- Approaches tried: 1 (axiomatic infrastructure → reduce to Prokhorov)

## Blockers

- **Disk pressure** (1.4 GiB free as of 2026-04-27) blocks Docker build verification.
- `multiple_recurrence_ge3` axiom remains TIER S blocked (~2000+ lines, requires
  ergodic decomposition + compact extension; out of scope for this problem instance).

## Next Action

1. Search Mathlib for `LevyProkhorov.completeSpace` or equivalent (~5 min).
2. Search Mathlib for `tendsto_measure_of_tendsto_of_isClopen` (~5 min).
3. If both exist: Path A becomes ~50 lines; the density preservation becomes a one-liner.
4. If neither exists: Path B via Banach-Alaoglu + Riesz, ~150 lines.

## Mathlib API Findings (Session 4)

Available:
- `instance MetrizableSpace (ProbabilityMeasure X)` (LevyProkhorovMetric.lean:717)
- `instance FirstCountableTopology.seq_compact_of_compact` (Topology/Sequences.lean:273)
- `IsTightMeasureSet.of_compactSpace` (Tight.lean:101)
- `WeakDual.isCompact_closedBall` (Analysis/Normed/Module/WeakDual.lean:47)
- `LevyProkhorov.probabilityMeasureHomeomorph` (LevyProkhorovMetric.lean:695)

Missing (confirmed by grep):
- No `instance CompactSpace (ProbabilityMeasure X)` for compact metrizable separable X
- No direct sequential Prokhorov theorem
