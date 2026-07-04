# Research State: ramsey-r4k-extensions-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-03
**Iteration**: 12 (PART XII)

## Current Focus
Extended the concrete deletion witnesses to k=8 (`deletion_no_mono_K8`, R(8,8)>45) with
its union-bound cap `unionBound_caps_at_42_for_K8` (R(8,8)>42). The +1 (k=6), +2 (k=7),
+3 (k=8) gain pattern is now witnessed at three consecutive k, all Tier-A axiom-free.
`n=46` is the top of the M=1 window for k=8, so this is the max `ramsey_deletion_one_past`
yields there.

## Active Approach
Machine-verified concrete witnesses (docker-build clean, 7744 jobs), Tier-A axiom-free
(`propext / Classical.choice / Quot.sound`). k=8 binomials (≈10⁸) evaluated via
`Nat.choose_eq_descFactorial_div_factorial` to keep kernel `decide` cheap and axiom-free.

## Attempt Count
- Total attempts: 12
- Current approach attempts: 1
- Approaches tried: LLL parameters, dependency-degree bound, LLL vs union bound
  identity, honest union-bound comparison (VII), deletion method (VIII), k=7
  machine-checked witness + compile repair (IX), general M=1 gain theorem (X),
  avoidance_pos numeric premises (XI), k=8 witness via descFactorial (XII)

## Blockers
- **MATH**: `SymmetricLLLForRamsey` full formalization (>1000 lines, measure theory) —
  the sole remaining non-Mathlib ingredient. Left as explicit hypothesis. See sibling
  `lovasz-local-lemma-oq-01`.

## Next Action
Optional future increments: (a) a general "deletion strictly beats union" corollary
quantifying the gain as a function of k (the +1/+2/+3 pattern suggests the gain grows
with k); (b) k=9 witness via the descFactorial route. The core deletion-method programme
is stated at full generality (M=0 recovers first moment via
`ramsey_deletion_generalizes_first_moment`; M=1 via `ramsey_deletion_one_past`), with
concrete axiom-free witnesses now at k=6,7,8.
