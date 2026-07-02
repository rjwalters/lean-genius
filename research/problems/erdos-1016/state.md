# Current State

**Phase**: ACT
**Since**: 2026-06-05
**Iteration**: 5

## Current Focus

Extend the grounded `SimpleGraph (Fin n)` pancyclic model: extract the
extreme-length cycle corollaries and establish that the grounded excess
`h_G = |E(G)| - n` is a well-defined, finite quantity (a two-sided
sandwich), replacing the vacuous abstract `pancyclicExcess`.

## Active Approach

Build directly on the grounded `HasCycleOfLength` / `IsPancyclicGraph`
definitions and the non-vacuous edge lower bound `n ≤ |E(G)|` that a
prior iteration proved. New, all 0-axiom / 0-sorry verified:

- `pancyclicGraph_hasHamiltonianCycle` — length-`n` cycle from pancyclicity
- `pancyclicGraph_hasTriangle` — length-`3` cycle from pancyclicity
- `pancyclicGraphExcess` (def) `= |E(G)| - n`
- `pancyclicGraphExcess_add` — `h_G + n = |E(G)|` (no ℕ truncation)
- `pancyclicGraphExcess_le` — `h_G ≤ C(n,2) - n`
  (via `card_edgeFinset_le_card_choose_two`)

Together with `ℕ` non-negativity this gives `0 ≤ h_G ≤ C(n,2) - n`,
so `h(n)` is well-defined and finite in the corrected model.

## Blockers

None for the grounded model's structural / boundedness lemmas.

The deep estimates `h(n) ≥ log₂(n−1) − 1` (Griffin 2013) and
`h(n) ≤ log₂ n + log* n + O(1)` (GKW 2016) remain open targets: they
require the doubling argument / hierarchical construction over concrete
`SimpleGraph (Fin n)` families, well beyond the crude sandwich above.

## Next Action

Attack a first genuine strengthening of the lower bound in the grounded
model, e.g. `h(n) ≥ 1` for `n ≥ 4` (a pancyclic graph is strictly more
than a single Hamiltonian cycle), en route to the Griffin doubling bound.

## Attempt Counts

- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0
