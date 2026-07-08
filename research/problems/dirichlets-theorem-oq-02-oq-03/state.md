# Research State: dirichlets-theorem-oq-02-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-08T14:15:19-07:00
**Iteration**: 2

## Current Focus
Deliverable complete: certified iterated-factorial tower bound on the k-th prime
≡ 3 (mod 4), verified 0 sorry / 0 axiom.

## Active Approach
Interval form of the Euclid construction → `Nat.find` enumeration `p3` → induction to the
tower `B(0)=3, B(k+1)=4·(B(k)+1)!−1`, giving `p3 k ≤ B k`.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
None for the certified elementary bound. Sharpening toward the true `p_k ∼ 2k·ln k`
provably requires analytic PNT-for-APs input (out of scope for the elementary argument).

## Next Action
Optional follow-ups: formalize the counting-function (density) side; attempt to lower the
certified tower toward exponential while staying elementary.
