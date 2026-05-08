# Current State

**Phase**: ACT (formalization complete; mathematics open)
**Since**: 2026-05-04T11:20:13Z
**Iteration**: 8

## Current Focus

Formalization is complete on `origin/main`:
`proofs/Proofs/Erdos831Problem.lean` — 717 lines, 0 sorries, 1 axiom.

The single axiom `erdos_831_growing : ∀ k, ∃ N, ∀ n ≥ N, h n ≥ k` IS the
open Erdős conjecture itself. Gallery `meta.json` correctly reflects
`status: "axiomatized"`, `badge: "axiom"`, `axiomCount: 1`.

## Active Approach

None active. The formalization phase is complete pending a mathematical
breakthrough on the open conjecture, which is out of scope for any single
Lean session.

## Blockers

- The Erdős conjecture h(n) → ∞ is genuinely OPEN — there is no Mathlib path.
- Quantitative lower bounds on h(n) (the actual estimate Erdős asked for)
  require new mathematics, not just Lean engineering.

## Next Action

None for this slug. Tractable bounded extensions exist but should be
considered separately:

1. Add base-case theorems `h_zero : h 0 = 0`, `h_one : h 1 = 0`,
   `h_two : h 2 = 0` (currently absent; provable via pigeonhole on
   `card S ≥ 3` requirement for any triple).
2. Upgrade the h(4) = 1 docstring into a formal theorem by formalizing
   the equilateral-triangle-plus-circumcenter construction (substantial
   coordinate-geometry work, ~200-300 lines).
3. Formalize the orchard configuration and unitDistanceProblem stubs
   (defined but unused; pruning vs proof choice).

None of these would discharge the open `erdos_831_growing` axiom.

## Attempt Counts

- Total attempts: 8
- Current approach attempts: 1
- Approaches tried: 8 (all converged to current axiomatized state)

## Approaches Tried (chronological)

1. Initial structure + h_upper_bound stub (PR #7326, 2026-03-28)
2. Proof architecture refactor (PR #7788, 2026-03-29)
3. circumradiusOf S₃ permutation invariance (PR #7799)
4. Metadata/sorry-count audit cycles (#7797, #7819, #7822, #7832)
5. h_upper_bound full proof + countDistinctRadii fix (S2-S5)
6. h_three full proof via standard triangle 27/81-case GP analysis (S6)
7. h(4) ≥ 2 axiom correction → h(4) = 1 (PR #15646, 2026-05-04)
8. Replace stale axioms with `erdos_831_growing` open-conjecture axiom (PR #15625, 2026-05-04)
