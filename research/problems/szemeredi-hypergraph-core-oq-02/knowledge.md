# Knowledge: szemeredi-hypergraph-core-oq-02

## Established Facts (verified, 0-axiom)

The file `Proofs/SzemerediHypergraphCoreOQ02.lean` verifies the **energy-increment
engine** of the hypergraph regularity lemma:

- `partitionEnergy s w d = ∑ wᵢ·dᵢ²` — the weighted mean-square density potential.
- `partitionEnergy_nonneg`, `partitionEnergy_le_one` — energy ∈ [0,1] for probability
  weights and densities in [-1,1].
- `energy_ge_of_steps` — E m ≥ E₀ + m·δ while all steps irregular.
- `energy_increment_bounded_steps` — a [0,1] energy boosted by ≥δ at each irregular
  step reaches a regular state within ⌈1/δ⌉ steps.
- `parts_le_pow` — per-step ×f blow-up ⇒ parts n ≤ parts₀·fⁿ (needs 1 ≤ f).
- `hypergraph_regularity_engine` — capstone: a regular partition with
  ≤ parts₀·f^⌈1/δ⌉ parts, conditional on the density-increment input.

`#print axioms` on the main theorems → only `propext, Classical.choice, Quot.sound`.

## Open Questions Within This Problem

- The genuinely open core: prove the Gowers/Rödl–Skokan hypergraph **density-increment
  inequality** on `relativeDensity` (OQ-01) — irregular ⇒ a complex refinement boosts
  `partitionEnergy` by ≥δ multiplying parts by ≤f. Discharging it turns
  `hypergraph_regularity_engine` into the full regularity lemma.

## Promising Leads

- Prove the graph (k=2) density increment first → fully verified graph regularity
  lemma in the `partitionEnergy` formulation, a stepping stone to the hypergraph case.
- Instantiate `partitionEnergy` with the concrete `kPartiteDensity`/`relativeDensity`.

## Failed Approaches

- Attempting the full lemma directly is intractable (wowzer-type bounds, not in Mathlib).
  The productive move was to isolate and verify the outer iteration engine and pin the
  inner analytic step to a single explicit hypothesis.
