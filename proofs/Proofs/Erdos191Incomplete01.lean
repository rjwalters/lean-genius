import Mathlib

/-
  # Erdős #191 — eliminating the `tripleLog_unbounded` axiom

  The gallery entry `erdos-191` (`Erdos191Problem.lean`) formalizes Erdős
  Problem #191 (monochromatic sets with large `∑ 1/log x`) and its known
  solution, carrying four axioms for the deep results. One of those axioms is
  *not* deep — it is the elementary fact that

      `tripleLog n = log(log(log n)) → ∞`   as `n → ∞`,

  stated there as `tripleLog_unbounded : ∀ M, ∃ N, ∀ n ≥ N, tripleLog n > M`.

  This file **proves** it (0 axioms, 0 sorries), so the axiom can be retired:
  the natural cast `ℕ → ℝ` tends to `atTop`, `Real.log` tends to `atTop` along
  `atTop`, and the threefold composition therefore tends to `atTop`; a `Tendsto …
  atTop` statement immediately gives the `∀ M, ∃ N, ∀ n ≥ N, … > M` form.

  (Proved standalone because `Erdos191Problem.lean` does not currently compile
  against this Mathlib under its declared imports — several supporting imports,
  e.g. `Real.log_two_gt_d9` and `rpow`, are missing there — so this entry
  re-states `tripleLog` and supplies the elementary divergence axiom-free,
  ready to drop in once those imports are repaired.)

  ## Results
  * `tripleLog_tendsto_atTop` : `log(log(log n)) → ∞`.
  * `tripleLog_unbounded`     : the `ε`-`N` form matching the parent's axiom.

  `0` axioms.
-/

namespace Erdos191Incomplete01

open Filter Real

/-- `log log log n`, the natural scale of Erdős #191 (matching the parent definition). -/
noncomputable def tripleLog (n : ℕ) : ℝ :=
  Real.log (Real.log (Real.log n))

/-- **Triple log diverges.** As `n → ∞`, `log(log(log n)) → ∞`: the cast
`ℕ → ℝ` tends to `atTop`, and `Real.log` preserves `atTop`, so the threefold
composition does too. -/
theorem tripleLog_tendsto_atTop :
    Tendsto (fun n : ℕ => tripleLog n) atTop atTop := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hcast))
  simpa only [Function.comp_def, tripleLog] using h

/-- **`tripleLog_unbounded`, axiom-free.** For every threshold `M` there is `N`
beyond which `tripleLog n > M`. This is exactly the statement axiomatized as
`tripleLog_unbounded` in `Erdos191Problem.lean`, here derived from
`tripleLog_tendsto_atTop`. -/
theorem tripleLog_unbounded : ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, tripleLog n > M := by
  intro M
  have h := tripleLog_tendsto_atTop.eventually (eventually_gt_atTop M)
  rw [eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn => hN n hn⟩

end Erdos191Incomplete01
