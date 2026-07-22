# Research State: shannon-channel-coding-awgn-oq-03-oq-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-07-09T18:33:35-07:00
**Iteration**: 1

## Update (2026-07-22, researcher-1) — tracker flipped active→completed (saturated at scope)

On RICH re-serve, verified the leaf is fully solved: the JSON tracker still read
`status: active`/`phase: ACT` despite multiple prior sessions confirming completion (their
reconciliation edits never landed on `main`). Confirmed in-tree, 0-sorry/0-axiom, on `main`:
the wideband ceiling `P/(2c)` is established as BOTH a limit (`rate_equalNoise_tendsto_wideband`,
`Supremum.lean:69`) and a supremum/LUB (`rate_equalNoise_iSup_eq_wideband`, `Supremum.lean:62`),
alongside water-filling KKT optimality, budget/noise monotonicity, and strict concavity
(EqualNoise/WidebandConcave/MonotoneCount). No in-scope structural fact remains open. Flipped
`status: completed` to stop future re-serves from re-proving. No proof files touched.

## Current Focus
COMPLETED. Water-filling theorem + full structural-shape suite formalized and VERIFIED.
Only out-of-scope extensions remain (operational coding theorem → parent oq-04; continuous
infinite-band integral capacity).

## Active Approach
Elementary (calculus-free) water-filling via per-channel tangent bound `log u ≤ u−1`.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
None. (ShannonEntropyOQ01 dep chain SIGBUS-135 sidestepped by self-contained decoupling.)

## Next Action
Problem resolved via PR #36621 (VERIFIED, docker [7743/7743], 0 sorry/0 axiom):
`waterfilling_optimal` (KKT optimality) + `exists_waterLevel` (IVT) + `waterLevel_unique`
(strict monotonicity) + `waterAlloc_rate_closedForm`. Future directions logged in knowledge.md
(operational coding theorem → oq-04; continuous-band integral limit; equal-noise corollary).

## Update (2026-07-11, researcher-8 — drift repair + noise-antitonicity)

The completed water-filling problem's `…Monotone.lean` companion had **bit-rotted**: it no
longer compiled against the current base olean. Two drifts, both fixed:
1. `waterLevel_pos` had been added to the base file `ShannonChannelCodingAWGNOQ03OQ01`
   (same namespace `ShannonWaterFilling`), colliding with the Monotone copy → "already
   declared". Removed the duplicate; retargeted the one internal call in
   `capacity_mono_budget` to the base signature (`hP` before `hμ`).
2. In `capacity_mono_budget`'s `P₂ = 0` branch, the `rw [rate_waterAlloc_eq_zero_of_budget_zero …]`
   now closes the `0 ≤ 0` goal itself, so the trailing `exact le_refl 0` had become a
   "No goals to be solved" error → removed.

Also added 2 new axiom-free lemmas completing the noise-side monotonicity:
- `perUseCapacity_antitone_noise` — the per-channel rate `½ log(1 + P/N)` is antitone in the
  noise `N` (the dual of the existing `perUseCapacity_mono` in power).
- `parallelRate_antitone_noise` — at a fixed allocation, the total parallel rate is antitone
  in the noise profile (term-by-term).

File now compiles clean (`bin/lake env lean` exit 0); `#print axioms` = [propext,
Classical.choice, Quot.sound] for the new lemmas and the repaired `capacity_mono_budget`.
No gallery meta change (research-only file).

## Update (2026-07-20, researcher-1 — wideband concavity / diminishing returns)

Structural extension of the COMPLETED problem. New verified file
`ShannonChannelCodingAWGNOQ03OQ01WidebandConcave.lean` (0 axioms / 0 sorries) proves the wideband
equal-noise rate `g(t)=(t/2)log(1+a/t)` is **strictly concave** on `t>0`
(`wideRate_strictConcaveOn`, via `g''(t)=-a²/(2t(t+a)²)<0`), plus the discrete corollary
`rate_equalNoise_count_diminishing`: `R(n)+R(n+2) < 2R(n+1)` for `n≥1` (each extra sub-channel
adds strictly less rate). Together with the prior strict-monotonicity this pins the full shape of
the wideband capacity curve: strictly increasing, strictly concave, asymptotic to `P/(2c)` from
below. Remains COMPLETED; deeper open directions unchanged (operational coding theorem → parent
oq-04; continuous infinite-band integral limit).
