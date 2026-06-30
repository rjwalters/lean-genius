/-
# Erdős Problem #396 — OQ-04 → OQ-01 → OQ-01 → OQ-01 → OQ-02: the sharp central-binomial growth law `C(2n,n) ∼ 4ⁿ/√(πn)`

The parent `Erdos396OQ04OQ01OQ01OQ01` telescopes the Catalan recurrence into a closed
product and asks, as its second open question, whether the same recurrence yields the
**central-binomial telescoping product** `C(2n,n) = ∏_{k<n} 2(2k+1)/(k+1)` *and hence the
matching growth law* `C(2n,n) ∼ 4ⁿ/√(πn)`.

The telescoping product itself is already established (sibling entry
`Erdos396OQ04OQ01OQ01OQ02OQ02OQ01`, "central binomial coefficient as a telescoping Wallis
product"), which deliberately stops at the *elementary* bound `C(2n,n) < 4ⁿ` and uses **no
Stirling estimate**. This entry supplies the remaining, genuinely analytic half — the
**sharp asymptotic constant** — which is exactly the ingredient that needs Stirling's
formula:

* **`centralBinom_isEquivalent`** : `(C(2n,n) : ℝ) ~[atTop] 4ⁿ/√(πn)`,
* **`centralBinom_mul_sqrt_pi_div_four_pow_tendsto_one`** : `C(2n,n)·√(πn)/4ⁿ → 1`.

The derivation is pure `Asymptotics.IsEquivalent` algebra on Mathlib's Stirling equivalence
`Stirling.factorial_isEquivalent_stirling` (`n! ~ √(2nπ)·(n/e)ⁿ`): writing
`C(2n,n) = (2n)!/(n!)²`, substituting Stirling into numerator and denominator, the `(n/e)`
powers contribute `4ⁿ`, `√(4nπ)/(2nπ)` collapses to `1/√(πn)`, and the Stirling constants
cancel to `1`.

Two consequences:

* **`succ_mul_catalan_eq_centralBinom`** : `C(2n,n) = (n+1)·catalan n` — the bridge to the
  parent's Catalan product; together with the asymptotic it yields the **Catalan growth law**
  the parent's docstring states but never proves,
* **`catalan_isEquivalent`** : `(catalan n : ℝ) ~[atTop] 4ⁿ/(n·√(πn))` (i.e.
  `catalan n ∼ 4ⁿ/(√π · n^{3/2})`), with limit form
  **`catalan_mul_div_four_pow_tendsto_one`**.

Finally the asymptotic upper rate is complemented by the elementary *effective* lower bound

* **`four_pow_div_two_mul_le_centralBinom`** : `4ⁿ/(2n) ≤ C(2n,n)` (`n ≥ 1`),

from Mathlib's `Nat.four_pow_le_two_mul_self_mul_centralBinom`, valid for every `n` (not just
asymptotically), so `4ⁿ/(2n) ≤ C(2n,n) ∼ 4ⁿ/√(πn) < 4ⁿ`.

Reference: https://erdosproblems.com/396
-/

import Mathlib

open Filter Topology Real Nat Asymptotics

namespace Erdos396OQ04OQ01OQ01OQ01OQ02

/-- The Stirling approximation function for `n!`: `√(2nπ)·(n/e)ⁿ`. By Mathlib's
    `Stirling.factorial_isEquivalent_stirling`, `n! ~[atTop] stirlingFn n`. -/
noncomputable def stirlingFn (n : ℕ) : ℝ := Real.sqrt (2 * n * π) * (n / Real.exp 1) ^ n

/- ## The central binomial coefficient as a quotient of factorials -/

/-- `(C(2n,n) : ℝ) = (2n)! / (n! · n!)`. From `Nat.choose_mul_factorial_mul_factorial`
    with `2n - n = n`. -/
theorem centralBinom_eq_factorial_div (n : ℕ) :
    (centralBinom n : ℝ) = (2 * n)! / (n ! * n !) := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  have h2 : 2 * n - n = n := by omega
  rw [eq_div_iff (by positivity)]
  have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [h2] at this
  push_cast [← this]; ring

/- ## The key pointwise simplification of the Stirling quotient -/

/-- For `n ≥ 1`, the Stirling quotient that governs `C(2n,n) = (2n)!/(n!)²` simplifies in
    closed form: `stirlingFn (2n) / (stirlingFn n)² = 4ⁿ / √(πn)`. The `(n/e)` powers give
    `4ⁿ`, `√(4nπ)/(2nπ)` collapses to `1/√(πn)`. -/
theorem stirlingFn_quotient (n : ℕ) (hn : 1 ≤ n) :
    stirlingFn (2 * n) / (stirlingFn n * stirlingFn n) = 4 ^ n / Real.sqrt (π * n) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have he : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  have hsq : (Real.sqrt (2 * n * π)) ^ 2 = 2 * n * π := by rw [Real.sq_sqrt]; positivity
  unfold stirlingFn
  have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  rw [hcast]
  have h4 : Real.sqrt (2 * (2 * (n:ℝ)) * π) = 2 * Real.sqrt (n * π) := by
    rw [show 2 * (2 * (n:ℝ)) * π = 4 * (n * π) by ring, show (4:ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [h4]
  have hpow : ((2 * (n:ℝ)) / Real.exp 1) ^ (2 * n)
      = 4 ^ n * ((n:ℝ) / Real.exp 1) ^ (2 * n) := by
    rw [show (2 * (n:ℝ)) / Real.exp 1 = 2 * ((n:ℝ) / Real.exp 1) by ring, mul_pow,
        pow_mul, show ((2:ℝ)) ^ 2 = 4 by norm_num]
  rw [hpow,
      show (Real.sqrt (2 * (n:ℝ) * π) * ((n:ℝ) / Real.exp 1) ^ n)
          * (Real.sqrt (2 * (n:ℝ) * π) * ((n:ℝ) / Real.exp 1) ^ n)
        = (Real.sqrt (2 * (n:ℝ) * π)) ^ 2 * ((n:ℝ) / Real.exp 1) ^ (2 * n) by ring, hsq,
      show Real.sqrt (π * n) = Real.sqrt (n * π) by rw [mul_comm]]
  have hgne : ((n:ℝ) / Real.exp 1) ^ (2 * n) ≠ 0 := by positivity
  have hnpisq : Real.sqrt (n * π) ^ 2 = n * π := by rw [Real.sq_sqrt]; positivity
  field_simp
  nlinarith [hnpisq, Real.sqrt_nonneg ((n:ℝ) * π)]

/- ## The sharp central-binomial asymptotic -/

/-- **The sharp growth law.** `(C(2n,n) : ℝ) ~[atTop] 4ⁿ/√(πn)`.

    Writing `C(2n,n) = (2n)!/(n!)²` and substituting Mathlib's Stirling equivalence
    `Stirling.factorial_isEquivalent_stirling` into numerator and denominator via
    `IsEquivalent.comp_tendsto`, `IsEquivalent.mul` and `IsEquivalent.div`, then collapsing
    the Stirling quotient by `stirlingFn_quotient`. This is the analytic half of the open
    question that the elementary telescoping-product sibling left open. -/
theorem centralBinom_isEquivalent :
    (fun n : ℕ => (centralBinom n : ℝ)) ~[atTop] (fun n : ℕ => 4 ^ n / Real.sqrt (π * n)) := by
  have hstir := Stirling.factorial_isEquivalent_stirling
  have hφ : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id
  have h1 : (fun n : ℕ => ((2 * n)! : ℝ)) ~[atTop] (fun n : ℕ => stirlingFn (2 * n)) :=
    hstir.comp_tendsto hφ
  have h2 : (fun n : ℕ => (n ! : ℝ) * (n ! : ℝ)) ~[atTop]
      (fun n : ℕ => stirlingFn n * stirlingFn n) := hstir.mul hstir
  have hdiv : (fun n : ℕ => ((2 * n)! : ℝ) / ((n ! : ℝ) * (n ! : ℝ)))
      ~[atTop] (fun n : ℕ => stirlingFn (2 * n) / (stirlingFn n * stirlingFn n)) := h1.div h2
  have hcbL : (fun n : ℕ => (centralBinom n : ℝ))
      = (fun n : ℕ => ((2 * n)! : ℝ) / ((n ! : ℝ) * (n ! : ℝ))) := by
    ext n; exact centralBinom_eq_factorial_div n
  have hRHS : (fun n : ℕ => stirlingFn (2 * n) / (stirlingFn n * stirlingFn n))
      =ᶠ[atTop] (fun n : ℕ => 4 ^ n / Real.sqrt (π * n)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn using stirlingFn_quotient n hn
  rw [hcbL]
  exact hdiv.trans hRHS.isEquivalent

/-- **Limit form of the growth law.** `C(2n,n)·√(πn)/4ⁿ → 1`. -/
theorem centralBinom_mul_sqrt_pi_div_four_pow_tendsto_one :
    Tendsto (fun n : ℕ => (centralBinom n : ℝ) * Real.sqrt (π * n) / 4 ^ n) atTop (𝓝 1) := by
  have hz : ∀ᶠ n : ℕ in atTop, (4:ℝ) ^ n / Real.sqrt (π * n) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0:ℝ) < n := by positivity
    positivity
  have key := (Asymptotics.isEquivalent_iff_tendsto_one hz).mp centralBinom_isEquivalent
  refine key.congr' ?_
  filter_upwards with n
  simp only [Pi.div_apply]
  rw [div_div_eq_mul_div]

/- ## Bridge to the parent's Catalan product, and the Catalan growth law -/

/-- **Catalan bridge.** `C(2n,n) = (n+1)·catalan n`, from `catalan_eq_centralBinom_div` and
    `Nat.succ_dvd_centralBinom`. This identifies the central-binomial product of the sibling
    entry with the parent's Catalan product. -/
theorem succ_mul_catalan_eq_centralBinom (n : ℕ) :
    (n + 1) * catalan n = centralBinom n := by
  rw [catalan_eq_centralBinom_div, Nat.mul_div_cancel' (Nat.succ_dvd_centralBinom n)]

/-- `(n+1) ~[atTop] n`: the prefactor relating the Catalan and central-binomial products is
    asymptotically negligible. -/
theorem nat_succ_isEquivalent :
    (fun n : ℕ => ((n : ℝ) + 1)) ~[atTop] (fun n : ℕ => (n : ℝ)) := by
  refine (Asymptotics.isEquivalent_iff_tendsto_one ?_).2 ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn; positivity
  · have h0 : Tendsto (fun n : ℕ => (1:ℝ) / (n:ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hsum : Tendsto (fun n : ℕ => 1 + (1:ℝ) / (n:ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add h0
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Pi.div_apply]
    have : (n:ℝ) ≠ 0 := by positivity
    field_simp

/-- **The Catalan growth law** the parent's docstring states but never proves:
    `(catalan n : ℝ) ~[atTop] 4ⁿ/(n·√(πn))`, i.e. `catalan n ∼ 4ⁿ/(√π · n^{3/2})`.
    Immediate from `catalan n = C(2n,n)/(n+1)`, the central-binomial asymptotic, and
    `(n+1) ~ n`. -/
theorem catalan_isEquivalent :
    (fun n : ℕ => (catalan n : ℝ)) ~[atTop]
      (fun n : ℕ => 4 ^ n / ((n : ℝ) * Real.sqrt (π * n))) := by
  have hcat : (fun n : ℕ => (catalan n : ℝ))
      = (fun n : ℕ => (centralBinom n : ℝ) / ((n : ℝ) + 1)) := by
    ext n
    have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [eq_div_iff hne]
    have : ((n : ℝ) + 1) * (catalan n : ℝ) = (centralBinom n : ℝ) := by
      exact_mod_cast succ_mul_catalan_eq_centralBinom n
    linarith [this]
  rw [hcat]
  have hdiv := centralBinom_isEquivalent.div nat_succ_isEquivalent
  refine hdiv.trans ?_
  refine Filter.EventuallyEq.isEquivalent ?_
  filter_upwards with n
  simp only [Pi.div_apply]
  rw [div_div, mul_comm]

/-- **Limit form of the Catalan growth law.** `catalan n · (n·√(πn)) / 4ⁿ → 1`. -/
theorem catalan_mul_div_four_pow_tendsto_one :
    Tendsto (fun n : ℕ => (catalan n : ℝ) * ((n : ℝ) * Real.sqrt (π * n)) / 4 ^ n)
      atTop (𝓝 1) := by
  have hz : ∀ᶠ n : ℕ in atTop, (4:ℝ) ^ n / ((n : ℝ) * Real.sqrt (π * n)) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0:ℝ) < n := by positivity
    positivity
  have key := (Asymptotics.isEquivalent_iff_tendsto_one hz).mp catalan_isEquivalent
  refine key.congr' ?_
  filter_upwards with n
  simp only [Pi.div_apply]
  rw [div_div_eq_mul_div]

/- ## Effective elementary lower bound (valid for every `n`, not just asymptotically) -/

/-- **Effective lower bound.** `4ⁿ/(2n) ≤ C(2n,n)` for `n ≥ 1`, from Mathlib's
    `Nat.four_pow_le_two_mul_self_mul_centralBinom`. Together with the asymptotic and the
    sibling's `C(2n,n) < 4ⁿ`, this brackets `4ⁿ/(2n) ≤ C(2n,n) ∼ 4ⁿ/√(πn) < 4ⁿ`. -/
theorem four_pow_div_two_mul_le_centralBinom (n : ℕ) (hn : 1 ≤ n) :
    (4 : ℝ) ^ n / (2 * n) ≤ (centralBinom n : ℝ) := by
  have h := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have hcast : (4 : ℝ) ^ n ≤ 2 * n * centralBinom n := by exact_mod_cast h
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * n)]
  calc (4 : ℝ) ^ n ≤ 2 * n * centralBinom n := hcast
    _ = (centralBinom n : ℝ) * (2 * n) := by ring

/- ## Sanity checks -/

/-- `C(6,3) = 20`. -/
example : centralBinom 3 = 20 := by decide

/-- The Catalan bridge at `n = 3`: `C(6,3) = 4 · catalan 3 = 4 · 5 = 20`. -/
example : centralBinom 3 = 4 * catalan 3 := by
  have h := succ_mul_catalan_eq_centralBinom 3; omega

/-- The factorial quotient at `n = 3`: `C(6,3) = 6!/(3!·3!) = 720/36 = 20`. -/
example : (centralBinom 3 : ℝ) = (2 * 3)! / (3 ! * 3 !) := centralBinom_eq_factorial_div 3

end Erdos396OQ04OQ01OQ01OQ01OQ02
