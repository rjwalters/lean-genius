# Research State: euler-polyhedral-formula-oq-02-oq-01-oq-01

## Current State
**Phase**: SURVEY
**Path**: fast
**Since**: 2026-05-30
**Iteration**: 4
**Last re-verified**: 2026-06-01 (researcher-1, claim `researcher-97989`) — local Mathlib mirror at `2df2f0150c` (the v4.26.0 toolchain bump, also the local pin); upstream master tick deferred this session (no `git fetch` in worktree-scope). Per prior 2026-05-31 tick: 24h showed no curvature/Stokes/Gauss-Bonnet primitives landing in master at commit `40f05009d0`. Re-survey upstream master at the *next* claim cycle. Assessment unchanged: blocked.

## Current Focus
Refined Mathlib-gap analysis. Riemannian-metric and CovariantDerivative APIs have landed on Mathlib master since the parent file was written; the curvature + manifold-integration + Stokes stack remains the blocker. Re-verified 2026-05-31: no new curvature/Stokes/Gauss-Bonnet primitives in master in the 24h since the prior survey — assessment unchanged.

## Active Approach
None. Awaiting upstream Mathlib infrastructure or a deliberate decomposition (S² intermediate milestone) before any first-principles proof attempt is warranted.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- Mathlib v4.26.0 (the local pin) lacks even the Riemannian-metric typeclass.
- Mathlib master adds `IsRiemannianManifold`, `pathELength`, `CovariantDerivative`, but still has **no** Gaussian curvature, geodesic curvature, manifold integration, area form, de Rham forms, Stokes' theorem on manifolds with boundary, or smooth Euler characteristic.
- Each missing piece is upstream infrastructure (multi-month Mathlib contribution scale), so building locally would create a parallel API that will conflict with Mathlib's eventual choices.

## Next Action
Re-survey Mathlib master when (a) Gaussian curvature lands, (b) a Riemannian volume/area form lands, or (c) any form of Stokes on manifolds with boundary lands. Until then, the productive intermediate target is a **round-S² only** Gauss-Bonnet milestone (`K ≡ 1`, area = 4π), which avoids the curvature tensor entirely; track that as a candidate subproblem rather than working it in this slot.
