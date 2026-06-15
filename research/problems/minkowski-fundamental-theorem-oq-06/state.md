# Research State: minkowski-fundamental-theorem-oq-06

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14
**Iteration**: 2

## Current Focus
Mathlib gap confirmed at pin; constants pinned (symmetric threshold 2·ζ(n) → δ_n ≥
ζ(n)/2^(n-1)) and bound hierarchy + factor-2ζ(n) improvement verified. Full proof blocked
on Siegel mean-value; staged-hypothesis file and elementary 2^(-n) bound identified as
actionable targets.

## Active Approach
None active (Docker down → no build). Next session: ACT one of the two staged targets.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- Full proof: Siegel's mean-value theorem over SL_n(ℝ)/SL_n(ℤ) absent from Mathlib
  (>1000 LOC of missing measure theory on the space of unimodular lattices).
- Build: Docker unavailable this session (build-free ORIENT only).

## Next Action
Either (1) stage Siegel as an explicit hypothesis and prove the better-than-average ⇒
existence extraction (badge=axiom), or (2) ACT the elementary δ_n ≥ 2^(-n) saturation
bound from Mathlib alone. Both are Docker-gated.
