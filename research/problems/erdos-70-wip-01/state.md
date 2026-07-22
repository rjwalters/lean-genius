# Research State: erdos-70-wip-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-07-22
**Iteration**: 4

## Current Focus
Node complete at the surrogate level: `InfiniteRamsey3` proved from scratch
(iterated ultrafilter majorities over `hyperfilter ℕ`), so the formalized
(cardinality-surrogate) `erdos_70_conjecture` is an unconditional theorem,
together with all its specializations (ω, ω², tower, ε₀). 0 axioms, 0 sorries.

## Active Approach
None — completed. The only remaining direction is the faithful order-type
upgrade (see blockers / next steps in the tracker JSON).

## Attempt Count
- Total attempts: 4
- Approaches tried: 3 (closure lemmas; ε₀ fixed point; ultrafilter Ramsey build)

## Blockers
- True order-type partition relation (Erdős–Rado partition calculus): genuinely
  open core of Erdős #70; reopen bar "materially new mechanism required
  (Mathlib gains order-type-preserving homogeneous-set machinery)".

## Next Action
Optional follow-up (new node): faithful order-type arrow for β = ω — provable
from `InfiniteRamsey3` since any infinite subset of a well-ordered set contains
an ω-chain. Materially weaker than the parent target (ω² onward needs
Erdős–Rado), hence valid decomposition, not an equivalent-strength restatement.
