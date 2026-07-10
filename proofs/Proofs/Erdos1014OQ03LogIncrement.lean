/-
Erdős Problem #1014 OQ-03: the *logarithmic* increment of the off-diagonal Ramsey
number, `Λ_l(k) := log R(k, l+1) − log R(k, l)`.

Companion to `Erdos1014OQ03.lean`, which proved the **increment–ratio bridge**:
for a positive sequence `R`, the normalized increment `(R(l+1) − R(l))/R(l)` tends
to `0` iff the consecutive ratio `R(l+1)/R(l)` tends to `1`, and applied this to
Erdős #1014's proven ratio-convergence `R(k,l+1)/R(k,l) → 1` to obtain the honest
increment consequence `Δ_l(k) = o(R(k,l))`.

This file adds the third equivalent quantity — the **log-increment**, which is the
natural measure of *smoothness* raised in OQ-03's open questions ("whether the
increment is monotone or eventually smooth"). The key identity is that the
log-increment equals `log` of the consecutive ratio,

    log R(l+1) − log R(l) = log ( R(l+1) / R(l) ),

so by continuity of `log`/`exp` the log-increment tends to `0` **iff** the ratio
tends to `1`. Chaining with the parent's bridge gives the three-way equivalence

    log-increment → 0   ⟺   ratio → 1   ⟺   normalized increment → 0 .

Applied to `R(k, ·)`, Erdős #1014's ratio-convergence therefore yields not only
`Δ_l(k) = o(R(k,l))` but also the smoothness statement
`log R(k,l+1) − log R(k,l) → 0` — the increment is asymptotically *log-flat*. The
full asymptotic formula for `Δ_l(k)` remains OPEN and is not asserted here.

Verified, 0 axioms, 0 sorries, no `native_decide`.
-/

import Mathlib
import Proofs.Erdos1014OQ03

namespace Erdos1014OQ03Log

open Filter Topology Erdos1014OQ03

/-- **Log-increment equals log of the ratio.** For an eventually-positive sequence
`R`, eventually `log R(l+1) − log R(l) = log ( R(l+1) / R(l) )`. -/
theorem log_increment_eventuallyEq_log_ratio (R : ℕ → ℝ)
    (hpos : ∀ᶠ l in atTop, 0 < R l) :
    (fun l => Real.log (R (l + 1)) - Real.log (R l))
      =ᶠ[atTop] (fun l => Real.log (R (l + 1) / R l)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpos
  filter_upwards [eventually_ge_atTop N] with l hl
  have h0 : 0 < R l := hN l hl
  have h1 : 0 < R (l + 1) := hN (l + 1) (by omega)
  rw [Real.log_div h1.ne' h0.ne']

/-- **Log-increment / ratio bridge.** For an eventually-positive sequence `R`, the
log-increment `log R(l+1) − log R(l)` tends to `0` **iff** the consecutive ratio
`R(l+1)/R(l)` tends to `1`.

Applied to `R(k, ·)`, the right-hand side is Erdős #1014's ratio-convergence
`R(k,l+1)/R(k,l) → 1`, so the increment is asymptotically log-flat:
`log R(k,l+1) − log R(k,l) → 0`. -/
theorem logIncrement_tendsto_zero_iff_ratio_tendsto_one (R : ℕ → ℝ)
    (hpos : ∀ᶠ l in atTop, 0 < R l) :
    Tendsto (fun l => Real.log (R (l + 1)) - Real.log (R l)) atTop (𝓝 0) ↔
      Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 1) := by
  rw [tendsto_congr' (log_increment_eventuallyEq_log_ratio R hpos)]
  constructor
  · -- `log(ratio) → 0`  ⟹  `ratio → 1`, via `ratio = exp (log ratio)`.
    intro h
    have hexp : Tendsto (fun l => Real.exp (Real.log (R (l + 1) / R l))) atTop (𝓝 1) := by
      have := (Real.continuous_exp.tendsto 0).comp h
      simpa using this
    have hEq : (fun l => Real.exp (Real.log (R (l + 1) / R l)))
        =ᶠ[atTop] (fun l => R (l + 1) / R l) := by
      obtain ⟨N, hN⟩ := eventually_atTop.mp hpos
      filter_upwards [eventually_ge_atTop N] with l hl
      have h0 : 0 < R l := hN l hl
      have h1 : 0 < R (l + 1) := hN (l + 1) (by omega)
      exact Real.exp_log (div_pos h1 h0)
    exact (tendsto_congr' hEq).mp hexp
  · -- `ratio → 1`  ⟹  `log(ratio) → 0`, by continuity of `log` at `1`.
    intro h
    have hlog : Tendsto Real.log (𝓝 1) (𝓝 (Real.log 1)) :=
      (Real.continuousAt_log (by norm_num)).tendsto
    have := hlog.comp h
    simpa using this

/-- **Three-way equivalence.** The log-increment tends to `0` iff the normalized
increment tends to `0` (both being equivalent to the ratio tending to `1`). Thus
the two natural "smoothness" measures of a positive sequence agree in the limit. -/
theorem logIncrement_tendsto_zero_iff_increment_div_tendsto_zero (R : ℕ → ℝ)
    (hpos : ∀ᶠ l in atTop, 0 < R l) :
    Tendsto (fun l => Real.log (R (l + 1)) - Real.log (R l)) atTop (𝓝 0) ↔
      Tendsto (fun l => (R (l + 1) - R l) / R l) atTop (𝓝 0) :=
  (logIncrement_tendsto_zero_iff_ratio_tendsto_one R hpos).trans
    (increment_div_tendsto_zero_iff_ratio_tendsto_one R
      (hpos.mono fun _ hl => hl.ne')).symm

/-- **Corollary (log-flatness).** If the consecutive ratio tends to `1` then the
log-increment tends to `0`. Fed Erdős #1014's `R(k,l+1)/R(k,l) → 1`, it delivers
`log R(k,l+1) − log R(k,l) → 0`. -/
theorem logIncrement_tendsto_zero_of_ratio_tendsto_one (R : ℕ → ℝ)
    (hpos : ∀ᶠ l in atTop, 0 < R l)
    (hratio : Tendsto (fun l => R (l + 1) / R l) atTop (𝓝 1)) :
    Tendsto (fun l => Real.log (R (l + 1)) - Real.log (R l)) atTop (𝓝 0) :=
  (logIncrement_tendsto_zero_iff_ratio_tendsto_one R hpos).mpr hratio

end Erdos1014OQ03Log
