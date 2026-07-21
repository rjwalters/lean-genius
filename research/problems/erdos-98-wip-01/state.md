# Research State: erdos-98-wip-01

## Current State
**Phase**: COMPLETED (for the `h 5 = 3` sub-goal)
**Path**: full
**Since**: 2026-07-21
**Iteration**: (see knowledge.md session log)

## Current Focus
`h 5 = 3` is **fully proved, docker-verified, axiom-free** (`h_five_eq_three`, this session).
The lower bound `h 5 ≥ 3` (`three_le_h_five`) is closed. The overall Erdős #98 conjecture
(`h(n)/n → ∞`) remains open — only the exact value `h 5` was in reach here.

## Active Approach — CLOSED
The anticipated "C₅ endgame" (2-regular ⟹ single 5-cycle ⟹ regular pentagon ⟹ concyclic)
was **bypassed entirely**. Key realization: 2-regularity gives every vertex a *constant row
sum of squared distances* `∑ₖ dist(Pᵢ,Pₖ)² = 2a²+2b²`. A centroid identity
(`25‖Pᵢ−O‖² = 5·rowᵢ − ½∑ₖrowₖ`) then forces `‖Pᵢ−O‖² = (a²+b²)/5` **independent of `i`**,
so all five points are equidistant from the centroid `O = ⅕∑Pₖ` — concyclic — contradicting
`NoFourConcyclic`. No cyclic order, no pentagon rigidity, no graph-connectivity fact needed.

## Attempt Count
- See knowledge.md session log.

## Blockers
None for `h 5 = 3` — proved. The remaining open targets are the *asymptotic* Erdős #98
statements (weak `h(n) ≥ n`, strong `h(n)/n → ∞`), which are genuinely open in mathematics
and not attackable by these elementary methods.

## Next Action — FOLLOW-UPS (h 5 done)
1. **`h 6`** — is `h 6 = 3` reachable? The centroid/row-sum method only kills *regular*
   2-distance sets; irregular 2-distance 6-sets need more.
2. **Regular two-distance sets are cospherical (general `n`/dimension)** — the centroid
   row-sum lemma proved here is dimension- and `n`-agnostic; extract as a standalone lemma.
