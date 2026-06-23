# Research State: erdos-476-oq-05

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15T15:38:43-07:00
**Iteration**: 2

## Current Focus
Two open sorries remain in `Erdos476OQ05Aristotle.lean`, both Aristotle targets:
- `ap_sdiff_endpoint` (was line 114): AP set-difference endpoint lemma.
- line ~269 (case1_exists `|B|≥3` branch): Dyson e-transform induction, ~150–200 LOC.

## Active Approach
Correctness audit of the helper lemmas before delegating to Aristotle.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- Aristotle backend 404 (live-probed) — cannot delegate the two HARD sorries.
- Local `.lake` is a circular self-symlink (0 oleans); Docker saturated (5 containers,
  incl 7h zombie) — cannot Docker-verify a hand proof this cycle.

## Key Finding (this session)
`ap_sdiff_endpoint` was stated with `0 < AP₁.card`, which makes it **FALSE**.
Counterexample (p=7, d=1): AP₂={0,1,2}, AP₁={4}. Then (AP₁\AP₂).card=1, n+m≤p,
but s₁=4 is neither s₂−d=6 nor s₂+(m−n+1)d=3. Corrected hypothesis: `2 ≤ AP₁.card`.
Full correct proof blueprint (d⁻¹-rescale to intervals mod p, wrap/no-wrap val split)
is inlined as a comment above the sorry. The lemma is currently unused (it is intended
support for the line-269 Dyson e-transform step), so the hypothesis strengthening is safe.

## Next Action
When Aristotle is non-404 OR a Docker trough (≤2 containers) opens:
1. Submit/hand-prove the corrected `ap_sdiff_endpoint` (now a TRUE statement).
2. Then attack the line-269 Dyson e-transform induction (blueprint in knowledge.md).
Do NOT re-submit the original `0 < AP₁.card` form — Aristotle would return the n=1
counterexample, not a proof.
