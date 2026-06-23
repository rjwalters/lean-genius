# Literature: shapley-folkman-oq-03 — Economic Application Formalization

## Core Papers

### Starr (1969) — The key economic application
- **Title**: "Quasi-equilibria in markets with non-convex preferences"
- **Journal**: Econometrica, 37(1), 25–38
- **Key result**: For an exchange economy with N agents in ℝ^d,
  the gap between a quasi-equilibrium and a true equilibrium is bounded by √d · max diam / N
- **Why relevant**: This is exactly the formal statement for OQ-03

### Shapley & Shubik (1966) — Original memo
- **Title**: Convexification result (unpublished memo, circulated 1966)
- **Published as**: Ross M. Starr extended and published the result in 1969

### Anderson (1978) — Elementary proof
- **Title**: "An elementary core equivalence theorem"
- **Journal**: Econometrica, 46(6), 1483–1487
- **Why relevant**: Cleaner proof of the norm bound, may be easier to formalize

## Related Gallery Proofs

- **shapley-folkman**: Base Shapley-Folkman Lemma
  - `proofs/Proofs/ShapleyFolkman.lean` — 814 lines, 1 sorry remaining
  - Contains: `sum_close_to_convexHull`, `repeated_sum_nearly_convex`
  - The economic theorems `sum_close_to_convexHull` and `repeated_sum_nearly_convex`
    are ALREADY PROVED — OQ-03 extends to the metric (norm) bound

## Lean / Mathlib Resources

- `Mathlib.Analysis.Convex.Hull` — `convexHull`, `subset_convexHull`
- `Mathlib.Analysis.Convex.Caratheodory` — Carathéodory theorem
- `Mathlib.Analysis.InnerProductSpace.Basic` — `‖·‖`, `inner_mul_le_norm_sq_mul_norm_sq`
- `Mathlib.Topology.MetricSpace.Basic` — `Metric.diam`, `Metric.diam_le_iff`
- `Mathlib.Analysis.MeanInequalities` — norm inequalities

## Approach Notes

The proof plan is:
1. Extract ≤ d excess components via `sum_close_to_convexHull`
2. For each excess component, bound ‖f i - nearestPoint Sᵢ (f i)‖ ≤ diam(conv(Sᵢ))
3. Apply Cauchy-Schwarz: ‖∑_{excess} vᵢ‖² ≤ |excess| · ∑ ‖vᵢ‖²
4. Conclude ‖∑ vᵢ‖ ≤ √d · max diam

Key Lean challenge: connecting `Metric.diam` to the inner product norm ‖·‖.
