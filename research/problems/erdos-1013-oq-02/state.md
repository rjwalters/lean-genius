# Research State: erdos-1013-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-05
**Iteration**: 5

## Current Focus (Iteration 5, 2026-07-05)
Packaged the pinch into its **sharpest user-facing form** in
`Erdos1013UnconditionalRatio.lean` (0 sorry / 0 axiom, Docker lean 4.26.0 VERIFIED,
first-try build). Three new theorems:
- `ratio_tendsto_imp_one` (general PolyBounded): if the consecutive ratio converges to `L`,
  then `L = 1`, **with no boundedness side-condition** — a convergent sequence is
  automatically bounded on both sides, so the cobounded hypotheses of `ratio_liminf_le_one`
  / `one_le_ratio_limsup` come for free via `Tendsto.isBoundedUnder_ge` / `isBoundedUnder_le`,
  and `Tendsto.liminf_eq` / `limsup_eq` collapse the straddle to `L ≤ 1 ≤ L`.
- `ratio_not_tendsto_of_ne_one` (contrapositive): the ratio does not converge to any `L ≠ 1`.
- `h3_ratio_tendsto_imp_one` (`h₃` specialisation): purely from `k² ≤ h₃(k) ≤ k³`, no
  bounded-ratio leaf and no constant hypothesis, any limit of `h₃(k+1)/h₃(k)` equals `1`.

This is strictly cleaner than iteration-4's `h3_ratio_liminf_le_one_le_limsup` (which needed
externally-supplied `m`, `M` bounds): convergence supplies its own two-sided boundedness. It
is the most direct unconditional statement toward the open (⋆): the ratio *cannot converge to
anything but `1`*. File now 21 theorems, 476 lines.

## Prior Iteration (4)
Promoted the frequency straddle to the **honest `Filter.liminf`/`Filter.limsup` form**:
`ratio_liminf_le_one`, `one_le_ratio_limsup`, `ratio_liminf_le_one_le_limsup`, and the `h₃`
specialisation `h3_ratio_liminf_le_one_le_limsup`. Given the ratio is eventually two-sided
bounded (the `[1/2,2]` bounded-ratio leaf supplies this cobounded side-condition),
`liminf_k h₃(k+1)/h₃ k ≤ 1 ≤ limsup_k h₃(k+1)/h₃ k` as genuine `Filter` statements.

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
