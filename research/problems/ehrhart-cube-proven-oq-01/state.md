# Research State: ehrhart-cube-proven-oq-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-05-08T09:30:00+03:00
**Iteration**: 2

## Current Focus
Problem fully solved across two sessions:
- S1 (2026-05-06): main theorem `simplex_lattice_count : |Sym (Fin (d+1)) n| = C(n+d, d)`
  via `Sym.card_sym_eq_choose` + binomial symmetry — PR #16233 merged.
- S2 (2026-05-08): polynomial-form section (descFactorial, ascFactorial, prod)
  exhibiting the count as an explicit degree-d polynomial in n.

## Active Approach
Closed: depth-first multiset bijection + ascending/descending factorial bridge to
`Nat.choose`. No further work planned on this problem.

## Attempt Count
- Total attempts: 2
- Current approach attempts: 2
- Approaches tried: 1 (multiset bijection — succeeded both sessions)

## Blockers
None.

## Next Action
Mark candidate-pool entry "completed". Two follow-up OQs deferred (see knowledge.md):
product polytopes (OQ-01) and Polynomial-typed lift (OQ-02).
