# Research State: borsuk-ulam-oq-02-oq-01-oq-01

## Current State
**Phase**: COMPLETE
**Path**: full
**Since**: 2026-04-05T00:00:00Z
**Iteration**: 1

## Current Focus
Formalization complete. 9 theorems, 1 axiom, 0 sorries.

## Active Approach
- Defined buDimFormula(n,d) = primeFactors(n).sup(buDim · d)
- Proved lower bound via Finset.sup_le + Nat.mem_primeFactors + buDim_mono
- Axiomatized upper bound (the open conjecture)
- Derived specific cases for n=4,6,9 using native_decide

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
None. Build successful.

## Next Action
Done. Committed and PR updated.
