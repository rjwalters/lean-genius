# Current State

**Phase**: FORMALIZED (verified infrastructure; open problem itself remains open)
**Since**: 2026-06-25
**Iteration**: 3

## Current Focus

Formalized the exact arithmetic of mediant insertion on Farey gaps:
`proofs/Proofs/Erdos1005ProblemOQ02.lean` (317 lines, 19 theorems, 1 def,
0 sorries, 0 axioms; #print axioms reports only propext / Classical.choice /
Quot.sound).

## Active Approach

Two verified threads:
1. **Gap-splitting calculus** — a unimodular gap `1/(bd)` splits under its
   mediant into `1/(b(b+d))` and `1/(d(b+d))`; these sum back to `1/(bd)`,
   stand in ratio `d:b`, and each is strictly smaller than the whole. Each
   half is again unimodular (recursive Stern–Brocot insertion).
2. **Minimal-denominator theorem (headline)** — every fraction `p/q` strictly
   between two unimodular neighbours `a/b < c/d` has `q ≥ b+d`, with equality
   forcing `p/q = (a+c)/(b+d)`. The mediant is the unique smallest-denominator
   fraction in the gap; `b+d` is a hard lower bound on any refinement.

## Blockers

The actual open question — improving the lower bound `f(n) ≥ (1/12 − o(1))n`
on the longest run of *similarly ordered* Farey fractions — is **not**
addressed. That constant `c ∈ [1/12, 1/4]` remains open. This session
formalizes the verified mediant calculus that such constructions rest on, not
a resolution of the bound.

## Iteration 3 addition (verified)

Added **§5 (strict denominator growth + depth-two refinement)**, 0-sorry /
0-axiom: `interior_denom_gt_max` (every in-gap fraction has denominator
> max(b,d) — refinement strictly raises the smallest denominator);
`denom_ge_left_subgap`/`denom_ge_right_subgap` (each sub-gap is again
unimodular, giving depth-two bounds q ≥ 2b+d, q ≥ b+2d); and the headline
`denom_ge_of_between_ne_mediant` — the mediant is the *unique* denominator-(b+d)
point, and the next admissible denominator jumps by ≥ min(b,d). This is the
strict-growth step the counting argument rests on; the 1/12 run constant itself
remains open.

## Next Action

A counting argument over consecutive mediant insertions, combined with the
gap-splitting and minimal-denominator results here, is the natural route
toward recovering (or improving) the `1/12` run lower bound.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
