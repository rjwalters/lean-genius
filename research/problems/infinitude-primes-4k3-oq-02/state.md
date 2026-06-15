# Research State: infinitude-primes-4k3-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14T20:50:00-07:00
**Iteration**: 2

## Current Focus
Mathlib-API-grounded feasibility survey complete. Approach pinned (character
orthogonality + per-character analytic asymptotic). Crux lemma M2 is gated.

## Active Approach
Davenport-style PNT-AP: indicator-decomposition by Dirichlet characters (M1,
buildable) + per-character prime asymptotic `Σ_{p≤x} χ(p)=o(π(x))` (M2, gated).

## Attempt Count
- Total attempts: 0 (no build — Docker DOWN)
- Current approach attempts: 0
- Approaches tried: 1 (literature/API survey, ORIENT)

## Blockers
- **M2 analytic crux absent from Mathlib**: the quantitative PNT-AP asymptotic
  `π(x;d,a)=(1/φ(d))Li(x)+o(·)` / `Σ_{p≤x}χ(p)=o(π(x))` for `χ≠χ₀` is an explicit
  **future** goal of the PNT+ project, not yet merged. Building from scratch is
  >1000 LOC / multi-month. This gates even the `d=4` milestone.
- **Docker build blackout**: cannot build the M1 orthogonality scaffold this session.

## Next Action
- Hold `surveyed` (stated cleanly; not provable until M2 lands).
- When Docker returns: build M1 (character-orthogonality indicator decomposition,
  ~80–150 LOC) citing Mathlib's `MulChar` orthogonality lemma.
- Watch PNT+ for the merged PNT-AP asymptotic; that unblocks M2 and the `d=4`
  milestone (`π(x;4,1) ∼ π(x;4,3) ∼ ½π(x)`).
