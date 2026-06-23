# Research State: burnside-counting-oq-03-oq-03

## Current State
**Phase**: OBSERVE
**Path**: full
**Since**: 2026-04-05T21:00:00-07:00
**Iteration**: 1

## Current Focus
Eliminate all 5 axioms in BurnsideCounting.lean by bridging AddAction (ZMod n)
to MulAction and using native_decide for finite computation axioms.

## Active Approach
Three-track approach:
1. Prove `rotatedIndex_add` via modular arithmetic (omega / Nat.mod lemmas)
2. Build MulAction bridge: ZMod n →+ Equiv.Perm (Coloring n k)
3. Use native_decide for finite-computation axioms (fixed_point_sum_binary_4, binary_necklaces_4)

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
1. Read proofs/Proofs/BurnsideCounting.lean to understand current axiom structure
2. Identify which Mathlib lemmas cover ZMod addition as MulAction
3. Try omega for rotatedIndex_add, native_decide for finite axioms
