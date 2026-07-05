# Research State: fourier-series-oq-02-oq-03-wip-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-07-04T15:07:19-07:00
**Iteration**: 2

## Current Focus
Sharp constant in the Hölder Fourier-decay bound. The `1/2` **upper** bound is already
proven (0 sorries) in `FourierSeriesOQ02.lean`. This session established that the WIP's
"`1/2` is sharp" goal is **false**: the true Lipschitz sharp constant is `4/π² ≈ 0.405`.

## Active Approach
Corrected Target #1 — formalize the **triangle-wave** lower bound
`∃ f, HolderWith 1 1 f ∧ ‖fourierCoeff f 1‖ = T/π²` (⟹ `k(1) ≥ 4/π² > 1/π`),
disproving the `1/2`-sharpness claim by exhibiting the true extremizer.

## Attempt Count
- Total attempts: 1 (ORIENT survey + paper analysis)
- Current approach attempts: 0 (Lean not yet written)
- Approaches tried: 0

## Blockers
- **Verification tooling down (session 2026-07-04):** Docker build unsafe (host swap 98%,
  SIGBUS risk); Aristotle MCP returns `Resource not found`. No Lean can be verified/committed.

## Next Action
When a build path is available, implement Corrected Target #1 (triangle-wave lower bound).
It is self-contained: define `Λ` on `AddCircle T`, prove `HolderWith 1 1 Λ`, compute
`fourierCoeff Λ 1` (either directly, or via `ĉ_1(Λ) = (T/2πi)·ĉ_1(Λ')` with `Λ' = ±1 square wave,
`ĉ_1(Λ') = 2/π`). See knowledge.md "Corrected, provable targets".
