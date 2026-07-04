# Research State: ramsey-r4k-extensions-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-04
**Iteration**: 13 (PART XIII)

## Current Focus
Unified the deletion hierarchy into a single general theorem `ramsey_deletion_window`:
for any window index M with `M·2^C(k,2) ≤ 2·C(n,k) < (M+1)·2^C(k,2)`, deletion certifies
`R(k,k) > n − M`. The two prior special-case theorems are now one-line corollaries with
unchanged signatures: `ramsey_deletion_generalizes_first_moment` = M=0,
`ramsey_deletion_one_past` = M=1. Concrete k=6/7/8 witnesses unchanged. Tier-A axiom-free.

## Active Approach
Machine-verified concrete witnesses (docker-build clean, 7744 jobs), Tier-A axiom-free
(`propext / Classical.choice / Quot.sound`). k=8 binomials (≈10⁸) evaluated via
`Nat.choose_eq_descFactorial_div_factorial` to keep kernel `decide` cheap and axiom-free.

## Attempt Count
- Total attempts: 13
- Current approach attempts: 1
- Approaches tried: LLL parameters, dependency-degree bound, LLL vs union bound
  identity, honest union-bound comparison (VII), deletion method (VIII), k=7
  machine-checked witness + compile repair (IX), general M=1 gain theorem (X),
  avoidance_pos numeric premises (XI), k=8 witness via descFactorial (XII),
  general M-window unification theorem (XIII)

## Blockers
- **MATH**: `SymmetricLLLForRamsey` full formalization (>1000 lines, measure theory) —
  the sole remaining non-Mathlib ingredient. Left as explicit hypothesis. See sibling
  `lovasz-local-lemma-oq-01`.

## Next Action
The axiom-free deletion line is now at a natural stopping point: the mechanism is stated
at full generality (`ramsey_deletion_window` for every window index M), with M=0/M=1
corollaries and concrete k=6,7,8 witnesses. Further k=9+ witnesses would be enumeration
theater (no new mathematics). The one genuinely valuable — but hard — remaining direction
is the BLOCKED `SymmetricLLLForRamsey` measure-theory construction (>1000 lines): the
probability space + mutual-independence `hindep`. A possible but analytically nontrivial
increment would quantify how the window width (hence the deletion gain over the sharp
union optimum) grows with k, which needs binomial-ratio estimates rather than `decide`.
