# Research State: erdos-1013-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-05
**Iteration**: 3

## Current Focus
Added the unconditional **straddle-1** result to `Erdos1013UnconditionalRatio.lean`:
for every `ε > 0` the consecutive ratio `h₃(k+1)/h₃(k)` is `< 1+ε` infinitely often
**and** `> 1−ε` infinitely often, i.e. `liminf ≤ 1 ≤ limsup`. This upgrades the earlier
`[1/2,2]` bounded-ratio leaf to a tight straddle of 1 — the ratio cannot drift away from
1 on either side; if the open pointwise (⋆) fails, it fails **only by oscillation**.

## Active Approach
Extract the pointwise shadow of the already-proved averaged (Cesàro) result. The engine
is two Cesàro sign lemmas: a vanishing Cesàro mean of the log-ratios cannot be eventually
`≥` a fixed positive constant nor eventually `≤` a fixed negative one. Applying these to
`log(1±ε)` gives the two frequency statements.

## Attempt Count
- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: 2

## Blockers
- Pointwise ratio → 1 is genuinely open: the `≈ log log k`-wide band between the known
  upper/lower bounds permits `O(log log k)` local oscillation. The straddle result now
  rules out one-sided *drift*, so the sole remaining obstruction is genuine *local
  variation* `|log h₃(k+1) − log h₃(k)| = o(1)`, which the current window cannot supply.

## Next Action
Either improve the upper bound to `(c+o(1))·k²·log k` (removes the gap), or find a direct
`h₃(k) ↔ h₃(k+1)` local-variation relation. Neither in reach now — the verified
straddle result is the deliverable for this iteration.

## This Iteration (2026-07-05)
- New theorems (all 0 sorry / 0 axiom, Docker lean 4.26.0 VERIFIED):
  `cesaro_ge_imp`, `cesaro_le_imp` (Cesàro sign lemmas),
  `ratio_frequently_lt`, `ratio_frequently_gt` (liminf ≤ 1 ≤ limsup),
  `h3_ratio_straddles_one` (h₃ specialisation).
- File now 14 theorems, 354 lines. `#print axioms` = propext/Classical.choice/Quot.sound.
