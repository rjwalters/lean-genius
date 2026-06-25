# Current State

**Phase**: FORMALIZED (verified infrastructure; open problem itself remains open)
**Since**: 2026-06-25
**Iteration**: 2

## Current Focus

Formalized the exact arithmetic of mediant insertion on Farey gaps:
`proofs/Proofs/Erdos1005ProblemOQ02.lean` (256 lines, 13 theorems, 1 def,
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

## Next Action

A counting argument over consecutive mediant insertions, combined with the
gap-splitting and minimal-denominator results here, is the natural route
toward recovering (or improving) the `1/12` run lower bound.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
