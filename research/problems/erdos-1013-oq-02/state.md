# Research State: erdos-1013-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-05
**Iteration**: 5

## Current Focus
Added the unconditional **polynomial growth-exponent bracket** to
`Erdos1013UnconditionalRatio.lean`. New theorems (0 sorry / 0 axiom, Docker lean 4.26.0
VERIFIED):
- `log_div_log_eventually_le` (general): for polynomially bounded `h` of degree `d`, the
  normalized log `log(h k)/log k ≤ d + ε` eventually — i.e. the *upper growth exponent* is
  `≤ d`.  This refines the engine `log(h k)/k → 0` (subexponential) to *sub-degree-`d`
  polynomial* growth; the only slack is the vanishing correction `log B/log k → 0`.
- `h3_log_exponent_between_two_three` (`h₃`): from the exact bounds `k² ≤ h₃(k) ≤ k³`
  alone, the sharp bracket `2 ≤ log(h₃ k)/log k ≤ 3` eventually (no `ε` — the bounding
  monomials have leading coefficient `1`, so `log` of each bound is exactly `2·log k`,
  `3·log k`).  This is the exponent-level shadow of the conjectured scale `h₃(k) ≍ k²·log k`
  (exponent `2`, sub-polynomial `log k` correction), unconditional and independent of (⋆).

File now 20 theorems, 501 lines. `#print axioms` = propext / Classical.choice / Quot.sound.

## Prior Iteration (4)
Promoted the frequency straddle to the **honest `Filter.liminf`/`Filter.limsup` form**:
`ratio_liminf_le_one`, `one_le_ratio_limsup`, `ratio_liminf_le_one_le_limsup`, and the `h₃`
specialisation `h3_ratio_liminf_le_one_le_limsup`. Given the ratio is eventually two-sided
bounded (the `[1/2,2]` bounded-ratio leaf supplies this cobounded side-condition), we now
have `liminf_k h₃(k+1)/h₃ k ≤ 1 ≤ limsup_k h₃(k+1)/h₃ k` as genuine `Filter` statements —
so **if the ratio converges at all, the limit is forced to be `1`**.

## Prior Iteration (3)
Added the unconditional **straddle-1** frequency result: for every `ε > 0` the ratio is
`< 1+ε` infinitely often **and** `> 1−ε` infinitely often. If the open pointwise (⋆) fails,
it fails **only by oscillation**.

## Active Approach
Extract the pointwise shadow of the already-proved averaged (Cesàro) result, then package
it in standard order-theoretic form. The `Filter.liminf_le_of_frequently_le` /
`Filter.le_limsup_of_frequently_le` lemmas convert the "frequently `< 1±ε`" facts (for all
`ε`) into `liminf ≤ 1` / `1 ≤ limsup`, using only that the ratio is eventually two-sided
bounded (cobounded side-conditions), which the bounded-ratio leaf provides.

## Attempt Count
- Total attempts: 3
- Current approach attempts: 1
- Approaches tried: 3

## Blockers
- Pointwise ratio → 1 is genuinely open: the `≈ log log k`-wide band between the known
  upper/lower bounds permits `O(log log k)` local oscillation. The straddle (now in
  liminf/limsup form) rules out one-sided *drift* and forces any limit to equal 1, so the
  sole remaining obstruction is genuine *local variation*
  `|log h₃(k+1) − log h₃(k)| = o(1)`, which the current window cannot supply.

## Next Action
Either improve the upper bound to `(c+o(1))·k²·log k` (removes the gap), or find a direct
`h₃(k) ↔ h₃(k+1)` local-variation relation. Neither in reach now — the verified
liminf/limsup straddle is the deliverable for this iteration.

## This Iteration (2026-07-05, Iteration 4)
- New theorems (all 0 sorry / 0 axiom, Docker lean 4.26.0 VERIFIED, first-try build):
  `ratio_liminf_le_one`, `one_le_ratio_limsup` (general),
  `ratio_liminf_le_one_le_limsup` (conjunction),
  `h3_ratio_liminf_le_one_le_limsup` (h₃ specialisation, takes eventual two-sided ratio
  bounds and constructs `IsBoundedUnder` via anonymous constructor `⟨M, habove⟩`).
- File now 18 theorems, 432 lines. `#print axioms` = propext/Classical.choice/Quot.sound.

## Prior Iteration (3, 2026-07-05)
- New theorems: `cesaro_ge_imp`, `cesaro_le_imp` (Cesàro sign lemmas),
  `ratio_frequently_lt`, `ratio_frequently_gt`, `h3_ratio_straddles_one`.
- File was 14 theorems, 354 lines.
