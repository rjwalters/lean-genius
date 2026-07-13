# Research State: four-square-distribution-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14
**Iteration**: 2

## Current Focus
Orbit-counting analysis of the B_4 = (Z/2)^4 ⋊ S_4 action on four-square
solution vectors. Identified a clean, brute-force-verified candidate theorem and
its proof strategy.

## Active Approach
Orbit–stabilizer + Burnside accounting. Target theorem:
`numTypes(n) ≤ r_4(n)/8` for `n>0`, reduced to the stabilizer bound
`|Stab_{B_4}(v)| ≤ 48` for nonzero solution vectors `v`.

## Key Results (sympy-verified, n=1..400, see verify/verify_orbit_count.py)
- Jacobi `r_4(n)=8·σ*(n)` (recomputed, not assumed).
- Orbit-size formula `|orbit(t)| = 2^k · 4!/∏ m_v!` matches brute force.
- Orbit-sum identity `Σ_t |orbit(t)| = r_4(n)`.
- Minimum orbit size for `n>0` is exactly 8 (type `(0,0,0,√n)`).
- Clean bound `numTypes(n) ≤ r_4(n)/8`, no counterexamples; equality only at n=1.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (orbit–stabilizer accounting)

## Blockers
Lean transcription is Docker-gated (build environment unavailable this session).
No mathematical blocker: the target is finite, fully inside Mathlib's MulAction
/ orbit-stabilizer API. Estimated ~200-400 LOC.

## Next Action
ACT phase: formalize `numTypes`, the B_4 action, and the stabilizer bound
`|Stab(v)| ≤ 48` (v≠0) → orbit lower bound 8 → `numTypes(n) ≤ r_4(n)/8`.
Take Jacobi's `r_4` count as a hypothesis from the parent entry.
