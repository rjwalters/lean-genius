# Research State: chebyshev-pnt-bridge-oq-01-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-04
**Iteration**: 2

## Current Focus
Corrected-bound formalization. The pool's conjectured `p^{v_p} ≤ kn` was DISPROVED
(counterexamples for all k ≥ 3); the correct bound `p^{v_p} ≤ (kn)^{k-1}` is stated
and drafted.

## Active Approach
Legendre/Kummer: `v_p(C(kn;n,…,n)) = ∑_i (⌊kn/p^i⌋ − k⌊n/p^i⌋)`, each summand in
`[0,k−1]`, nonzero only for `p^i ≤ kn`, hence `v_p ≤ (k−1)·log_p(kn)` and
`p^{v_p} ≤ (kn)^{k−1}`.

## Attempt Count
- Total attempts: 1 (this session)
- Approaches tried: 1 (Legendre carry-digit route)

## Blockers
- Aristotle 404 (Resource not found) — cannot verify/delegate.
- Docker build historically down — cannot compile locally.
  → Build-independent session; drafted Lean is UNVERIFIED (honestly labeled).

## Next Action
Prove the single remaining sorry `central_multinomial_val_le_log` (blueprint in the
Lean file) — ideal Aristotle target once the 404 blackout lifts. Then verify the full
file and derive the π(kn) corollary.
