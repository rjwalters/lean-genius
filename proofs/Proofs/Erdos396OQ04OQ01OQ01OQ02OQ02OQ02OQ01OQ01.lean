/-
# Erdős Problem #396 — OQ-04 → OQ-01 → OQ-01 → OQ-02 → OQ-02 → OQ-02 → OQ-01 → OQ-01:
  the sharp Catalan asymptotic `Cₙ ∼ 4ⁿ / (√π · n^{3/2})`

Two long sub-threads of #396 have, separately, pinned the two halves of the
growth of the Catalan numbers `Cₙ`:

* the **exponent** thread proved, from the recurrence alone, that the
  normalised sequence carries the *critical exponent* `3/2`
  (`Cₙ / 4ⁿ ∼ n^{-3/2}`), the Catalan analogue of the central binomial's `1/2`;
* the **constant** thread (entry `…OQ02OQ02OQ02OQ01`) pinned the *exact*
  leading constant of the central binomial coefficient,
  `C(2n,n)·√n / 4ⁿ → 1/√π`.

This file fuses the two into the single sharp statement for the Catalan numbers
themselves.  Using the elementary identity `(n+1)·Cₙ = C(2n,n)`
(`succ_mul_catalan_eq_centralBinom`) and `n/(n+1) → 1`, the central-binomial
limit transports directly to

    `Cₙ · n·√n / 4ⁿ → 1/√π`        (`catalan_mul_pow_sqrt_div_tendsto`),

i.e. `Cₙ ∼ 4ⁿ / (√π · n^{3/2})` (`catalan_mul_sqrt_pi_div_tendsto_one`).
Here `n·√n` is the square-root-free spelling of `n^{3/2}`; the extra factor of
`n` over the central binomial's `√n` is exactly the `1/(n+1)` of the Catalan
normalisation, and it is what turns the `1/2` exponent into `3/2`.

## Method

The central-binomial limit is reproved self-contained through Mathlib's Stirling
sequence `stirlingSeq n = n! / (√(2n)·(n/e)ⁿ)` (`tendsto_stirlingSeq_sqrt_pi`),
via the single *square-root-free* bridge identity (for `n ≥ 1`)

    `C(2n,n)²·n / 16ⁿ = stirlingSeq(2n)² / stirlingSeq(n)⁴`        (`cb_sq_identity`).

Squaring removes every square root, the right side tends to `π/π² = 1/π`, and a
final square root transports the limit to `1/√π`.  The Catalan step is then a
purely algebraic factorisation `Cₙ·n·√n/4ⁿ = (C(2n,n)·√n/4ⁿ)·(n/(n+1))`
followed by `Tendsto.mul` with `n/(n+1) → 1`.

No Stirling *estimate* is hand-rolled.

Reference: https://erdosproblems.com/396
-/

import Mathlib

open Nat Filter Topology Finset Real Stirling

namespace Erdos396OQ01OQ01OQ02OQ02OQ02OQ01OQ01

/-! ## The factorial identity `(2n)! = C(2n,n)·(n!)²` -/

/-- `(2n)! = C(2n,n)·(n!)²`, cast to `ℝ`. -/
theorem two_mul_factorial_eq (n : ℕ) :
    ((2 * n)! : ℝ) = (centralBinom n : ℝ) * ((n ! : ℝ) * (n ! : ℝ)) := by
  have h : centralBinom n * (n ! * n !) = (2 * n)! := by
    have h2 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h2
    rw [show (2 * n).choose n = centralBinom n from rfl, mul_assoc] at h2
    exact h2
  exact_mod_cast h.symm

/-! ## The square-root free bridge identity -/

/-- **Bridge identity.** For `n ≥ 1`,
`C(2n,n)²·n / 16ⁿ = stirlingSeq(2n)² / stirlingSeq(n)⁴`. -/
theorem cb_sq_identity (n : ℕ) (hn : 1 ≤ n) :
    (centralBinom n : ℝ) ^ 2 * n / 16 ^ n
      = stirlingSeq (2 * n) ^ 2 / stirlingSeq n ^ 4 := by
  have hm : (0 : ℝ) < n := by exact_mod_cast hn
  have hSn : stirlingSeq n ^ 4
      = (n ! : ℝ) ^ 4
          / ((2 * (n : ℝ)) ^ 2 * ((n : ℝ) / Real.exp 1) ^ (4 * n)) := by
    have e1 : (√(2 * (n : ℝ))) ^ 4 = (2 * (n : ℝ)) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (by positivity)]
    have e2 : (((n : ℝ) / Real.exp 1) ^ n) ^ 4 = ((n : ℝ) / Real.exp 1) ^ (4 * n) := by
      rw [← pow_mul, mul_comm n 4]
    rw [stirlingSeq, div_pow, mul_pow, e1, e2]
  have hS2n : stirlingSeq (2 * n) ^ 2
      = ((centralBinom n : ℝ) * ((n ! : ℝ) * (n ! : ℝ))) ^ 2
          / ((2 * (2 * (n : ℝ)))
              * (16 ^ n * ((n : ℝ) / Real.exp 1) ^ (4 * n))) := by
    have e3 : (√(2 * ((2 * n : ℕ) : ℝ))) ^ 2 = 2 * (2 * (n : ℝ)) := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; ring
    have e4 : ((((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n)) ^ 2
        = 16 ^ n * ((n : ℝ) / Real.exp 1) ^ (4 * n) := by
      rw [← pow_mul, show (2 * n) * 2 = 4 * n by ring]
      push_cast
      rw [show (2 * (n : ℝ)) / Real.exp 1 = 2 * ((n : ℝ) / Real.exp 1) by ring, mul_pow,
          pow_mul (2 : ℝ) 4 n, show (2 : ℝ) ^ 4 = 16 by norm_num]
    rw [stirlingSeq, div_pow, mul_pow, e3, e4, two_mul_factorial_eq n]
  have hfac : (n ! : ℝ) ≠ 0 := by exact_mod_cast n.factorial_pos.ne'
  have hnne : (n : ℝ) ≠ 0 := hm.ne'
  have hPne : ((n : ℝ) / Real.exp 1) ^ (4 * n) ≠ 0 := by positivity
  have h16 : (16 : ℝ) ^ n ≠ 0 := by positivity
  rw [hS2n, hSn]
  field_simp

/-! ## The central binomial limit (engine) -/

/-- **The exact Wallis constant for `C(2n,n)`.**
`C(2n,n)·√n / 4ⁿ → 1/√π`. -/
theorem centralBinom_mul_sqrt_div_tendsto :
    Tendsto (fun n => (centralBinom n : ℝ) * √n / 4 ^ n) atTop (𝓝 (1 / √π)) := by
  have htends2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by show n ≤ 2 * n; omega) tendsto_id
  have h2 : Tendsto (fun n : ℕ => stirlingSeq (2 * n)) atTop (𝓝 (√π)) :=
    tendsto_stirlingSeq_sqrt_pi.comp htends2n
  have h2sq : Tendsto (fun n : ℕ => stirlingSeq (2 * n) ^ 2) atTop (𝓝 π) := by
    have := h2.pow 2
    rwa [Real.sq_sqrt Real.pi_nonneg] at this
  have h4 : Tendsto (fun n : ℕ => stirlingSeq n ^ 4) atTop (𝓝 (π ^ 2)) := by
    have := tendsto_stirlingSeq_sqrt_pi.pow 4
    rwa [show (√π) ^ 4 = π ^ 2 by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt Real.pi_nonneg]] at this
  have hπ2 : (π : ℝ) ^ 2 ≠ 0 := by positivity
  have hratio : Tendsto (fun n : ℕ => stirlingSeq (2 * n) ^ 2 / stirlingSeq n ^ 4)
      atTop (𝓝 (π / π ^ 2)) := h2sq.div h4 hπ2
  have hval : (π : ℝ) / π ^ 2 = 1 / π := by
    rw [sq, ← div_div, div_self Real.pi_ne_zero]
  rw [hval] at hratio
  have hfsq : Tendsto (fun n : ℕ => ((centralBinom n : ℝ) * √n / 4 ^ n) ^ 2)
      atTop (𝓝 (1 / π)) := by
    refine hratio.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← cb_sq_identity n hn, div_pow, mul_pow, Real.sq_sqrt (by positivity),
        show ((4 : ℝ) ^ n) ^ 2 = 16 ^ n by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  have hf := hfsq.sqrt
  have hsv : √(1 / π) = 1 / √π := by rw [one_div, Real.sqrt_inv, one_div]
  rw [hsv] at hf
  exact hf.congr (fun n => Real.sqrt_sq (by positivity))

/-! ## `n/(n+1) → 1` -/

/-- The Catalan-to-central-binomial weight `n/(n+1) → 1`. -/
theorem div_succ_tendsto_one :
    Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
  have hbase : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
    (tendsto_const_nhds).sub tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sub_zero] at hbase
  refine hbase.congr (fun n => ?_)
  have hne : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-! ## The sharp Catalan asymptotic -/

/-- **Sharp Catalan asymptotic.** With `n·√n` the square-root-free spelling of
`n^{3/2}`,
`Cₙ · n·√n / 4ⁿ → 1/√π`,
i.e. `Cₙ ∼ 4ⁿ / (√π · n^{3/2})`.  The extra factor `n` over the central
binomial's `√n` (entry `…OQ01`) carries the `1/2 ↦ 3/2` jump in the exponent. -/
theorem catalan_mul_pow_sqrt_div_tendsto :
    Tendsto (fun n => (catalan n : ℝ) * (n * √n) / 4 ^ n) atTop (𝓝 (1 / √π)) := by
  have hprod := centralBinom_mul_sqrt_div_tendsto.mul div_succ_tendsto_one
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  -- `(n+1)·Cₙ = C(2n,n)` over ℝ
  have hrel : ((n : ℝ) + 1) * (catalan n : ℝ) = (centralBinom n : ℝ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom n
  have hne : (n : ℝ) + 1 ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  -- factor `C(2n,n) = (n+1)·Cₙ` and split off `n/(n+1)`
  rw [← hrel]
  field_simp

/-! ## Consequences -/

/-- **Equivalent normalisation.** `Cₙ · √π · n·√n / 4ⁿ → 1`,
i.e. `Cₙ ∼ 4ⁿ / (√π · n^{3/2})`. -/
theorem catalan_mul_sqrt_pi_div_tendsto_one :
    Tendsto (fun n => (catalan n : ℝ) * (√π * (n * √n)) / 4 ^ n) atTop (𝓝 1) := by
  have hf := catalan_mul_pow_sqrt_div_tendsto
  have hmul := (tendsto_const_nhds (x := √π) (f := (atTop : Filter ℕ))).mul hf
  rw [show √π * (1 / √π) = 1 by
        rw [mul_one_div, div_self (Real.sqrt_ne_zero'.mpr Real.pi_pos)]] at hmul
  refine hmul.congr (fun n => ?_)
  ring

/-- **The limit constant is exactly that of the central binomial.** The sharp
Catalan constant `1/√π` coincides with the central-binomial constant of the
parent entry; the Catalan numbers inherit the Wallis constant unchanged, only
the exponent shifts `1/2 ↦ 3/2`. -/
theorem catalan_constant_eq_centralBinom_constant :
    (Tendsto (fun n => (catalan n : ℝ) * (n * √n) / 4 ^ n) atTop (𝓝 (1 / √π)))
      ∧ (Tendsto (fun n => (centralBinom n : ℝ) * √n / 4 ^ n) atTop (𝓝 (1 / √π))) :=
  ⟨catalan_mul_pow_sqrt_div_tendsto, centralBinom_mul_sqrt_div_tendsto⟩

end Erdos396OQ01OQ01OQ02OQ02OQ02OQ01OQ01

-- #print axioms Erdos396OQ01OQ01OQ02OQ02OQ02OQ01OQ01.catalan_mul_pow_sqrt_div_tendsto
