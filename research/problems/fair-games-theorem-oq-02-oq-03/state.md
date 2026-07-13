# Research State: fair-games-theorem-oq-02-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-05T02:10:00Z
**Iteration**: 2

## Current Focus
Quartic martingale Q(n, s) = s^4 - 6 n s^2 + 3 n^2 + 2 n is now defined
in `FairGamesTheoremOQ02OQ03.lean`. The pointwise step-mean identity
½Q(n+1, s+1) + ½Q(n+1, s-1) = Q(n, s) is proved by `ring`.

## Active Approach
Build the variance proof in three layers:
1. **Algebraic** (this iteration): the polynomial Q satisfies the
   step-mean martingale identity. ✅
2. **Probabilistic** (next): lift Q into the `MartingaleProcess`
   framework used in `FairGamesTheoremOQ02OQ01` to get OST.
3. **Closed-form**: solve the OST equation
     k^4 = E[S_τ^4] − 6 E[τ S_τ^2] + 3 E[τ^2] + 2 E[τ]
   for E[τ^2], using E[S_τ^4] = N^3 k.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- The residual quantity E[τ · 𝟙_{S_τ = N}] is not directly handled by
  the current martingale machinery — likely needs an auxiliary
  martingale or a generating-function detour.

## Next Action
Lift `quarticMartingaleValue` into a `MartingaleProcess`-typed quantity
matching the API used in `FairGamesTheoremOQ02OQ01`, then apply OST.
