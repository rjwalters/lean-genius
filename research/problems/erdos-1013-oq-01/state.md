# Current State

**Phase**: PARTIAL
**Since**: 2026-06-25
**Iteration**: 2

## Current Focus

Structural reduction between the two open parts of Erdős #1013.

## Active Approach

Rather than determine the exact constant c in h₃(k) ~ c·k²·log k (genuinely open,
c ∈ [1/2,1]), prove that the asymptotic-constant question subsumes the
ratio-convergence question: existence of c (any c > 0) implies h₃(k+1)/h₃(k) → 1.

## Result (verified, 0-axiom, original)

Proofs/Erdos1013ConstantRatio.lean — 4 theorems, 1 definition, 0 sorries, 0 axioms:

- `constant_unique`        — the asymptotic constant, if it exists, is unique.
- `scale_ratio_tendsto_one` — analytic core: ((k+1)²·log(k+1))/(k²·log k) → 1.
- `ratio_tendsto_one`      — h(k)/(k²·log k) → c > 0  ⇒  h(k+1)/h(k) → 1.
- `asymptotic_subsumes_ratio` — same statement phrased for the threshold h₃.

`#print axioms` reports only propext / Classical.choice / Quot.sound for all four.

## Blockers

The exact constant c remains open (requires extremal/probabilistic Ramsey-theoretic
input well beyond a single Lean development). The reduction proved here is the
tractable, honest contribution.

## Next Action

Open question for future work: prove ratio convergence directly without establishing
the full asymptotic, or determine whether c = 1/2.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
