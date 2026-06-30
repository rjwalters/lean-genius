import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Chebyshev bounds OQ-03: the second Chebyshev function ψ and its equivalence with θ

The parent entry (`chebyshev-bounds`) bounds the first Chebyshev function θ(x) = Σ_{p ≤ x} log p
and lists as an open question:

> *Formalize the second Chebyshev function ψ(x) = Σ_{p^k ≤ x} log p and show ψ(x) ∼ x ⟺
> π(x) ∼ x/log(x) via partial summation.*

Mathlib already defines `Chebyshev.psi` (`ψ`) and `Chebyshev.theta` (`θ`) and proves the
crucial size estimate `|ψ(x) − θ(x)| ≤ 2√x · log x`. This file uses it to establish the
first link of that chain rigorously: **ψ and θ are asymptotically equivalent**, so

`ψ(x)/x → 1  ⟺  θ(x)/x → 1`.

(The remaining link `θ(x) ∼ x ⟺ π(x) ∼ x/log x` is genuine partial-summation work pursued in
the sibling `chebyshev-pnt-bridge` entries.) The point is that ψ − θ collects only the prime
*powers* p^k with k ≥ 2, a set so sparse that `ψ(x) − θ(x) = o(x)`; hence the prime-power
correction is invisible to the leading asymptotic, and the second Chebyshev function carries
exactly the same `∼ x` content as the first.

## Main results

* `log_div_sqrt_tendsto_zero` : `log x / √x → 0`.
* `psi_sub_theta_div_tendsto_zero` : `(ψ(x) − θ(x))/x → 0` (the prime-power correction is `o(x)`).
* `psi_asymp_iff_theta_asymp` : `ψ(x)/x → 1 ⟺ θ(x)/x → 1`.
* `theta_le_psi'` / `abs_psi_sub_theta_le'` : the underlying order and size facts, restated.
-/

namespace ChebyshevBoundsOQ03

open Filter Asymptotics Chebyshev
open scoped Topology

/-- `θ(x) ≤ ψ(x)`: the second Chebyshev function dominates the first (restating
    `Chebyshev.theta_le_psi`), since ψ counts prime powers and θ only primes. -/
theorem theta_le_psi' (x : ℝ) : θ x ≤ ψ x := Chebyshev.theta_le_psi x

/-- The Chebyshev size estimate `|ψ(x) − θ(x)| ≤ 2√x·log x` (restating
    `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`). -/
theorem abs_psi_sub_theta_le' {x : ℝ} (hx : 1 ≤ x) :
    |ψ x - θ x| ≤ 2 * Real.sqrt x * Real.log x :=
  Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx

/-- `log x / √x → 0` as `x → ∞`: the logarithm grows slower than any positive power. -/
theorem log_div_sqrt_tendsto_zero :
    Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.sqrt_eq_rpow]

/-- **The prime-power correction is `o(x)`.** `(ψ(x) − θ(x))/x → 0`: the difference between
    the second and first Chebyshev functions, which counts only prime powers `p^k` with
    `k ≥ 2`, is asymptotically negligible compared to `x`. -/
theorem psi_sub_theta_div_tendsto_zero :
    Tendsto (fun x : ℝ => (ψ x - θ x) / x) atTop (𝓝 0) := by
  have hb : ∀ᶠ x : ℝ in atTop,
      ‖(ψ x - θ x) / x‖ ≤ 2 * Real.sqrt x * Real.log x / x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0]
    gcongr
    exact abs_psi_sub_theta_le' hx
  have hg : Tendsto (fun x : ℝ => 2 * Real.sqrt x * Real.log x / x) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => 2 * (Real.log x / Real.sqrt x)) atTop (𝓝 0) := by
      simpa using log_div_sqrt_tendsto_zero.const_mul 2
    refine Tendsto.congr' ?_ h0
    filter_upwards with x
    rw [show (2 : ℝ) * Real.sqrt x * Real.log x / x
          = (2 * Real.log x) * (Real.sqrt x / x) from by ring, Real.sqrt_div_self']
    ring
  exact squeeze_zero_norm' hb hg

/-- **ψ and θ carry the same leading asymptotic.** `ψ(x)/x → 1 ⟺ θ(x)/x → 1`: the prime
    number theorem in the form `ψ(x) ∼ x` is equivalent to `θ(x) ∼ x`, because the two
    Chebyshev functions differ by `o(x)`. -/
theorem psi_asymp_iff_theta_asymp :
    Tendsto (fun x : ℝ => ψ x / x) atTop (𝓝 1) ↔
    Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1) := by
  have hcorr := psi_sub_theta_div_tendsto_zero
  constructor
  · intro h
    have hsub := h.sub hcorr
    rw [sub_zero] at hsub
    refine hsub.congr fun x => ?_
    rw [div_sub_div_same]
    ring_nf
  · intro h
    have hadd := h.add hcorr
    rw [add_zero] at hadd
    refine hadd.congr fun x => ?_
    rw [div_add_div_same]
    ring_nf

end ChebyshevBoundsOQ03
