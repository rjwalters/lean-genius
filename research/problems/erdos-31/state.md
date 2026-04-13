# Current State

**Phase**: OBSERVE
**Since**: 2026-04-05
**Iteration**: 3

## Current Focus

Eliminate the remaining `axiom lorentz_theorem : Erdos31Statement` by formalizing
the Lorentz greedy construction. The 2026-03-27 session made significant progress:
coverage was fully proved, but `lorentzB_density_zero` remains sorry.

## Active Approach

Seeker-selected: Prove that the greedy Lorentz complement B has density zero.

**Key goal**: `lorentzB_density_zero` — show |B ∩ [0,N]| / N → 0.

The bound follows from the D-free structural property of lorentzB:
- No two B-elements b, b' differ by (a - a₀) for a ∈ A
- This limits how many B-elements can lie in [0,N] relative to |A ∩ [0,N]|
- Since A is infinite: |A ∩ [0,N]| → ∞, so |B ∩ [0,N]| / N → 0

**Research steps:**
1. Read current `Erdos31Problem.lean` (786 lines, 1 axiom) to understand existing defs
2. Check what `lorentzB_mem` definition looks like (if it exists in the file)
3. If the greedy construction from 2026-03-27 was lost: re-implement using well-founded recursion
4. Prove the density bound: use D-free property to count B ∩ [0,N] ≤ N / (sInf A spacing)

## Blockers

None.

## Next Action

1. Read full `proofs/Proofs/Erdos31Problem.lean` to understand current defs
2. Check if `lorentzB` recursive def exists or needs to be (re)built
3. Attempt density proof via D-free counting argument
4. If coverage proof is also lost: re-implement the greedy coverage argument

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 0
- Approaches tried: 1

## Formalization Status

- **File**: proofs/Proofs/Erdos31Problem.lean
- **Lines**: 786
- **Builds**: Yes (builds with 1 axiom)
- **Sorries**: 0
- **Axioms**: 1 (`lorentz_theorem`)
- **Key Definitions**: 10+
- **Proved Results**: 8+ (counting bounds, density lemmas, limit theorems)
