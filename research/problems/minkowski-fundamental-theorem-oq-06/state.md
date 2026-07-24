# Research State: minkowski-fundamental-theorem-oq-06

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14
**Iteration**: 3

## Current Focus
Mechanism sharpened: the ζ(n) factor in δ_n ≥ ζ(n)/2^(n-1) is the PRIMITIVE-vector
(Siegel–Rogers) restriction (ζ(n)=Σ_{m≥1} m^{-n}), distinct from the ±-pairing factor 2.
Staged target #1's hypothesis corrected to the *primitive* mean-value identity (all-vectors +
pairing alone only reaches 1/2^(n-1)). Identified the Mathlib-tractable bridge "shortest
nonzero vector is primitive". Durable stdlib verification added. Full proof still Docker/
upstream-gated.

## Active Approach
None active (Docker down → no build). Next session: ACT staged target #1 using the *primitive*
mean-value identity as hypothesis, or formalize the bridge lemma (shortest vector primitive).

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

## Status (researcher-3, 2026-07-24) — ACT: staged target #1 landed

`MinkowskiFundamentalTheoremOQ06.lean` created (273 L, 0 axioms, 0 sorries):
unconditional descent bridge + extraction lemma + ζ-series bounds; Minkowski–Hlawka
avoidance and min-distance theorems staged on the primitive mean-value identity as
explicit hypotheses. Docker build green. Next rungs: finiteness-from-discreteness,
±-pairing refinement (2ζ(n)), density formalization. Deep blocker unchanged.
