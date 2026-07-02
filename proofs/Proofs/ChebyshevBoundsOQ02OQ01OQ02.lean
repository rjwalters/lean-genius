import Mathlib
import Proofs.ChebyshevBoundsOQ02OQ01

/-!
# Chebyshev bounds OQ-02-OQ-01-OQ-02: transferring `ψ = Θ(x)` to `θ = Θ(x)`

The parent entry (`chebyshev-bounds-oq-02-oq-01`) proves the elementary two–sided estimate
`(log 2 / 3)·m ≤ ψ(m) ≤ (log 4 + 4)·m` for the **second** Chebyshev function, i.e. `ψ(x) = Θ(x)`.
This entry answers the open question of **transferring that growth rate to the first Chebyshev
function** `θ`, obtaining `θ(x) = Θ(x)`.

The transfer rests on two Mathlib facts:

* `Chebyshev.theta_le_psi` : `θ x ≤ ψ x` (θ counts only primes, ψ counts prime powers), and
* `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` : `|ψ x − θ x| ≤ 2√x·log x`.

The upper bound is immediate: `θ(x) ≤ ψ(x) ≤ (log 4 + 4)·x`.  For the lower bound we write
`θ(x) = ψ(x) − (ψ(x) − θ(x)) ≥ ψ(x) − 2√x·log x`.  Since the parent gives `ψ(x) ≥ (log 2 / 6)·x`
for `x ≥ 2` (bridging real `x` to `⌊x⌋₊`) and the correction `2√x·log x = o(x)`, eventually
`θ(x) ≥ (log 2 / 12)·x`.  Packaging both bounds as `Asymptotics.IsTheta` gives `θ =Θ[atTop] id`.

## Main results

* `theta_le_linear` : `θ(x) ≤ (log 4 + 4)·x` for `x ≥ 0`.
* `psi_ge_linear` : `(log 2 / 6)·x ≤ ψ(x)` for `x ≥ 2` (real lower bound via the floor bridge).
* `two_sqrt_mul_log_isLittleO` : `2√x·log x = o(x)`.
* `theta_ge_eventually` : eventually `(log 2 / 12)·x ≤ θ(x)`.
* `theta_isBigO_id` / `id_isBigO_theta` : the two `O`-bounds.
* `theta_isTheta_id` : **`θ =Θ[atTop] (fun x => x)`**, i.e. `θ(x) = Θ(x)`.
-/

namespace ChebyshevBoundsOQ02OQ01OQ02

open Filter Asymptotics Chebyshev
open scoped Topology

/-- `log x / √x → 0` as `x → ∞` (logarithm grows slower than any positive power).  This is the
Mathlib-only fact behind the `o(x)` correction; also proved in the sibling `ChebyshevBoundsOQ03`
but inlined here to keep this file's build surface to `Mathlib` + the parent. -/
theorem log_div_sqrt_tendsto_zero :
    Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.sqrt_eq_rpow]

/-- **Upper bound.** `θ(x) ≤ (log 4 + 4)·x` for `x ≥ 0`: since `θ ≤ ψ` and `ψ` is bounded by the
same linear function (`Chebyshev.psi_le_const_mul_self`). -/
theorem theta_le_linear {x : ℝ} (hx : 0 ≤ x) : θ x ≤ (Real.log 4 + 4) * x :=
  (Chebyshev.theta_le_psi x).trans (Chebyshev.psi_le_const_mul_self hx)

/-- **Floor bridge.** For real `x`, `ψ(x)` equals the parent's natural-number Chebyshev sum at
`⌊x⌋₊`, because both are `∑_{n ≤ ⌊x⌋₊} Λ(n)`. -/
theorem psi_eq_chebyshevPsi_floor (x : ℝ) :
    ψ x = ChebyshevBoundsOQ02.chebyshevPsi ⌊x⌋₊ := by
  rw [ChebyshevBoundsOQ02OQ01.chebyshevPsi_eq_psi, Chebyshev.psi_eq_sum_Icc,
    Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]

/-- **Real lower bound.** `(log 2 / 6)·x ≤ ψ(x)` for `x ≥ 2`.  We pass to `n := ⌊x⌋₊ ≥ 2`, use the
parent's `(log 2 / 3)·n ≤ ψ(n)`, and bound `n ≥ x − 1 ≥ x/2`. -/
theorem psi_ge_linear {x : ℝ} (hx : 2 ≤ x) : Real.log 2 / 6 * x ≤ ψ x := by
  set n := ⌊x⌋₊ with hn
  have hn2 : 2 ≤ n := by rw [hn]; exact Nat.le_floor (by exact_mod_cast hx)
  have hpsi_eq : ψ x = ChebyshevBoundsOQ02.chebyshevPsi n := psi_eq_chebyshevPsi_floor x
  have hlow : Real.log 2 / 3 * (n : ℝ) ≤ ChebyshevBoundsOQ02.chebyshevPsi n :=
    ChebyshevBoundsOQ02OQ01.chebyshevPsi_lower_linear hn2
  have hfloor_ge : x - 1 ≤ (n : ℝ) := by
    have h := Nat.lt_floor_add_one x
    rw [← hn] at h; linarith
  have hxhalf : x / 2 ≤ (n : ℝ) := by linarith
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc Real.log 2 / 6 * x = Real.log 2 / 3 * (x / 2) := by ring
    _ ≤ Real.log 2 / 3 * (n : ℝ) := mul_le_mul_of_nonneg_left hxhalf (by linarith)
    _ ≤ ChebyshevBoundsOQ02.chebyshevPsi n := hlow
    _ = ψ x := hpsi_eq.symm

/-- The prime-power correction is `o(x)`: `2√x·log x = o(x)` as `x → ∞`. -/
theorem two_sqrt_mul_log_isLittleO :
    (fun x : ℝ => 2 * Real.sqrt x * Real.log x) =o[atTop] (fun x : ℝ => x) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hdiv : Tendsto (fun x : ℝ => 2 * Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    have h := log_div_sqrt_tendsto_zero.const_mul (2 : ℝ)
    simpa [mul_div_assoc] using h
  filter_upwards [hdiv.eventually_le_const hc, eventually_ge_atTop (1 : ℝ)] with x hxc hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hsqrt_pos : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsqrt_sq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hprod_nonneg : (0 : ℝ) ≤ 2 * Real.sqrt x * Real.log x :=
    mul_nonneg (mul_nonneg (by norm_num) hsqrt_pos.le) hlogx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0.le, abs_of_nonneg hprod_nonneg]
  -- from `2 log x / √x ≤ c` (multiply by `√x > 0`) get `2 log x ≤ c·√x`
  have key : 2 * Real.log x ≤ c * Real.sqrt x := (div_le_iff₀ hsqrt_pos).mp hxc
  have h2 : 2 * Real.log x * Real.sqrt x ≤ c * Real.sqrt x * Real.sqrt x :=
    mul_le_mul_of_nonneg_right key hsqrt_pos.le
  calc 2 * Real.sqrt x * Real.log x
      = 2 * Real.log x * Real.sqrt x := by ring
    _ ≤ c * Real.sqrt x * Real.sqrt x := h2
    _ = c * x := by rw [mul_assoc, hsqrt_sq]

/-- Eventually `2√x·log x ≤ (log 2 / 12)·x`. -/
theorem two_sqrt_mul_log_le_eventually :
    ∀ᶠ x : ℝ in atTop, 2 * Real.sqrt x * Real.log x ≤ Real.log 2 / 12 * x := by
  have hc : (0 : ℝ) < Real.log 2 / 12 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  have h := two_sqrt_mul_log_isLittleO
  rw [Asymptotics.isLittleO_iff] at h
  filter_upwards [h hc, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0] at hx
  linarith [le_abs_self (2 * Real.sqrt x * Real.log x), hx]

/-- **Lower bound, eventual linear form.** Eventually `(log 2 / 12)·x ≤ θ(x)`. -/
theorem theta_ge_eventually :
    ∀ᶠ x : ℝ in atTop, Real.log 2 / 12 * x ≤ θ x := by
  filter_upwards [two_sqrt_mul_log_le_eventually, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop (1 : ℝ)] with x hxbound hx2 hx1
  have hpsi := psi_ge_linear hx2
  have habs := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1
  have hle : ψ x - θ x ≤ 2 * Real.sqrt x * Real.log x := (le_abs_self _).trans habs
  linarith [hpsi, hle, hxbound]

/-- **`θ = O(x)`.** -/
theorem theta_isBigO_id : (fun x : ℝ => θ x) =O[atTop] (fun x : ℝ => x) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨Real.log 4 + 4, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0,
    abs_of_nonneg (Chebyshev.theta_nonneg x)]
  exact theta_le_linear hx0

/-- **`x = O(θ)`.** -/
theorem id_isBigO_theta : (fun x : ℝ => x) =O[atTop] (fun x : ℝ => θ x) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨12 / Real.log 2, ?_⟩
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [theta_ge_eventually, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx0,
    abs_of_nonneg (Chebyshev.theta_nonneg x)]
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
  nlinarith [hx, hlog2]

/-- **Main result: `θ(x) = Θ(x)`.** The first Chebyshev function has the same linear growth rate
as the identity, transferred from `ψ(x) = Θ(x)`. -/
theorem theta_isTheta_id : (fun x : ℝ => θ x) =Θ[atTop] (fun x : ℝ => x) :=
  ⟨theta_isBigO_id, id_isBigO_theta⟩

end ChebyshevBoundsOQ02OQ01OQ02
