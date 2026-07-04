# Research State: ramsey-r4k-extensions-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-03
**Iteration**: 10 (PART X)

## Current Focus
Generalized the ad-hoc k=6/k=7 deletion witnesses into one k-uniform theorem
`ramsey_deletion_one_past`: whenever `n` is one step past the sharp union threshold
(`2^C(k,2) ≤ 2·C(n,k) < 2·2^C(k,2)`, i.e. deletion count `M=1`), the deletion method
keeps a monochromatic-Kₖ-free set of `n−1` vertices. Both concrete witnesses are now
instances of a stated mechanism.

## Active Approach
Machine-verified general theorem (docker-build clean, 7744 jobs), Tier-A axiom-free
(`propext / Classical.choice / Quot.sound`). The `M=1` collapse is proved by the two
`Nat` div-iff lemmas + `omega` (no large binomial `decide`).

## Attempt Count
- Total attempts: 10
- Current approach attempts: 1
- Approaches tried: LLL parameters, dependency-degree bound, LLL vs union bound
  identity, honest union-bound comparison (VII), deletion method (VIII), k=7
  machine-checked witness + compile repair (IX), general M=1 gain theorem (X)

## Blockers
- **MATH**: `SymmetricLLLForRamsey` full formalization (>1000 lines, measure theory) —
  the sole remaining non-Mathlib ingredient. Left as explicit hypothesis. See sibling
  `lovasz-local-lemma-oq-01`.

## Next Action
Optional future increments: (a) a general "deletion strictly beats union" corollary
quantifying the gain as a function of k; (b) k=8 witness via the descFactorial route.
The core deletion-method programme is now stated at full generality (M=0 recovers first
moment via `ramsey_deletion_generalizes_first_moment`; M=1 via `ramsey_deletion_one_past`).
