# Knowledge: fair-games-theorem-oq-02-oq-01-oq-01

## Problem Summary

**Goal**: Formalize Wald's Identity supporting lemmas via Mathlib.

The main file `FairGamesTheoremOQ03.lean` is already COMPLETE (0 sorries). This problem
focuses on closing the 11 sorries in `FairGamesTheoremOQ03Aristotle.lean`, which provides
routine supporting lemmas for automated proof search.

## Mathlib API Discovered

- `MeasureTheory.isStoppingTime_const ℱ N` — proves `IsStoppingTime ℱ (fun _ => N)` for `N : ℕ∞`
- `IsStoppingTime.min hτ hπ` (`hτ.min hπ`) — min of two stopping times is a stopping time
- `stoppedValue_const` — simp lemma reducing `stoppedValue f (fun _ => n)` to `f n`
- `ENNReal.toReal_le_one.mpr prob_le_one` — proves `(μ s).toReal ≤ 1` for probability measure
- `Submartingale.expected_stoppedValue_mono` — key monotonicity for optional stopping
- `simp [stoppedValue]` — unfolds `stoppedValue f τ ω`
- `simp [stoppedValue, min_eq_left h]` — proves stoppedValue equality when τ ≤ N

## Session 2026-04-23 (Session 1)

**Outcome**: progress
**Sorries closed**: 7 of 11 (pending CI verification)

### Proofs Written

1. `stoppedValue_const`: `simp [stoppedValue]`
2. `stoppedValue_eq_of_le`: `simp only [stoppedValue, min_eq_left h]`
3. `isStoppingTime_const`: `MeasureTheory.isStoppingTime_const ℱ N`
4. `isStoppingTime_min`: `hτ.min hπ`
5. `martingale_stopped_integral_eq`: sub/supermartingale sandwich (from main file)
6. `martingale_stopped_eq_initial`: sub/supermartingale sandwich (from main file)
7. `measure_toReal_le_one`: `ENNReal.toReal_le_one.mpr prob_le_one`

### Remaining Sorries (4)

1. `stoppedValue_measurable` — needs `Adapted.stoppedValue_measurable` or similar
2. `stoppedValue_integrable` — integrability from bounded stopping time
3. `doob_maximal_real_of_nnreal` — NNReal/ENNReal conversion of Doob maximal ineq
4. `maximal_set_measurable` — measurability of `{ω | ∃ n ≤ N, thresh ≤ f n ω}`
