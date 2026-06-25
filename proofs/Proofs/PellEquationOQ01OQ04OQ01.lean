import Mathlib

/-
# Pell Equation OQ-01-OQ-04-OQ-01: the regulator scales linearly along *all* integer powers

The parent entry `pell-equation-oq-01-oq-04` showed that the **Pell norm**
`pellNorm d x y = x + y√d` is a multiplicative homomorphism on Mathlib's group
of Pell solutions `Pell.Solution₁ d` (Brahmagupta's identity), so the
**regulator** `pellRegulator d a = log (pellNorm d a.x a.y)` is additive and, on
*non-negative* powers, scales linearly:

  `pellNorm (aⁿ) = (pellNorm a)ⁿ`,    `R(aⁿ) = n · R(a)`    (`n : ℕ`).

Because the Pell solutions form a **group** — the inverse of `(x, y)` is the
conjugate `(x, −y)` — it makes sense to raise a solution to a *negative* power,
and the parent's clean scaling laws ought to persist over all of `ℤ`. This entry
proves exactly that:

* `pellNorm_inv`        : **`pellNorm a⁻¹ = (pellNorm a)⁻¹`** — the norm of the
  conjugate is the reciprocal of the norm (the multiplicative shadow of
  `(x + y√d)(x − y√d) = 1`).
* `pellNorm_zpow`       : **`pellNorm (aⁿ) = (pellNorm a)ⁿ` for every `n : ℤ`** —
  the norm intertwines the group's integer-power operation with real
  `zpow`, negatives included.
* `pellRegulator_zpow`  : **`R(aⁿ) = n · R(a)` for every `n : ℤ`** — the regulator
  is genuinely a `ℤ`-linear function of the exponent.
* `pellRegulator_inv` / `pellRegulator_neg_one` / `pellRegulator_zpow_neg`:
  the negative-exponent corollaries (`R(a⁻¹) = −R(a)`, etc.).

The proof of the `zpow` law is an integer induction (`Int.induction_on`): the
forward step is the parent's `pellNorm_mul` together with `zpow_add_one₀` on the
real side; the backward step is the same multiplicativity applied to `a⁻¹`,
glued by `pellNorm_inv` and `zpow_sub_one₀`. The regulator law then drops out of
`Real.log_zpow`, which already turns real `zpow` into multiplication by the
exponent.

The supporting norm lemmas (`pellNorm_one`, `pellNorm_mul`, `pellNorm_mul_inv`,
`pellNorm_ne_zero`) are restated here so the file is self-contained; the genuinely
new content is the extension across `0` of the exponent line.

`0` axioms.
-/

namespace PellEquationOQ01OQ04OQ01

open Pell

/-- The Pell norm `x + y√d` (matching the parent definition). -/
noncomputable def pellNorm (d : ℤ) (x y : ℤ) : ℝ :=
  (x : ℝ) + (y : ℝ) * Real.sqrt (d : ℝ)

/-- The Pell regulator `log(x + y√d)` (matching the parent definition). -/
noncomputable def pellRegulator (d : ℤ) (a : Solution₁ d) : ℝ :=
  Real.log (pellNorm d a.x a.y)

variable {d : ℤ}

/-- The norm of the identity solution `(1, 0)` is `1`. -/
theorem pellNorm_one (d : ℤ) :
    pellNorm d (1 : Solution₁ d).x (1 : Solution₁ d).y = 1 := by
  rw [Solution₁.x_one, Solution₁.y_one]
  simp [pellNorm]

/-- **Brahmagupta's identity / norm multiplicativity.** For `d ≥ 0`,
`pellNorm (a·b) = pellNorm a · pellNorm b`. -/
theorem pellNorm_mul (d : ℤ) (hd : 0 ≤ d) (a b : Solution₁ d) :
    pellNorm d (a * b).x (a * b).y = pellNorm d a.x a.y * pellNorm d b.x b.y := by
  simp only [pellNorm, Solution₁.x_mul, Solution₁.y_mul]
  have hsq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast hd)
  push_cast
  linear_combination (-((a.y : ℝ) * (b.y : ℝ))) * hsq

/-- **The conjugate identity.** `pellNorm a · pellNorm a⁻¹ = 1`. -/
theorem pellNorm_mul_inv (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) :
    pellNorm d a.x a.y * pellNorm d a⁻¹.x a⁻¹.y = 1 := by
  rw [Solution₁.x_inv, Solution₁.y_inv]
  simp only [pellNorm]
  have hsq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast hd)
  have hprop : (a.x : ℝ) ^ 2 - (d : ℝ) * (a.y : ℝ) ^ 2 = 1 := by exact_mod_cast a.prop
  push_cast
  linear_combination hprop - ((a.y : ℝ) ^ 2) * hsq

/-- The Pell norm is never zero (its product with the inverse's norm is `1`). -/
theorem pellNorm_ne_zero (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) :
    pellNorm d a.x a.y ≠ 0 := by
  intro h
  have hkey := pellNorm_mul_inv d hd a
  rw [h, zero_mul] at hkey
  exact zero_ne_one hkey

/-- **The norm of the inverse is the reciprocal of the norm.** For `d ≥ 0`,
`pellNorm a⁻¹ = (pellNorm a)⁻¹`: since `pellNorm a · pellNorm a⁻¹ = 1`
(conjugate identity) and `pellNorm a ≠ 0`, the inverse's norm is forced to be
the multiplicative inverse. This is the seed that lets the scaling law cross
into negative exponents. -/
theorem pellNorm_inv (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) :
    pellNorm d a⁻¹.x a⁻¹.y = (pellNorm d a.x a.y)⁻¹ := by
  have hkey := pellNorm_mul_inv d hd a
  have hne := pellNorm_ne_zero d hd a
  have h1 : pellNorm d a⁻¹.x a⁻¹.y = 1 / pellNorm d a.x a.y := by
    rw [eq_div_iff hne, mul_comm]; exact hkey
  rw [h1, one_div]

/-- **The Pell norm intertwines integer powers with real `zpow`.** For `d ≥ 0`
and every integer exponent `n` (negative ones included),
`pellNorm (aⁿ) = (pellNorm a)ⁿ`. Proven by integer induction: the parent's
`pellNorm_mul` powers the forward step and the same identity applied to `a⁻¹`
(via `pellNorm_inv`) powers the backward step, matched on the real side by
`zpow_add_one₀` / `zpow_sub_one₀`. -/
theorem pellNorm_zpow (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) (n : ℤ) :
    pellNorm d (a ^ n).x (a ^ n).y = (pellNorm d a.x a.y) ^ n := by
  have hne : pellNorm d a.x a.y ≠ 0 := pellNorm_ne_zero d hd a
  refine Int.induction_on n ?_ ?_ ?_
  · simp [pellNorm]
  · intro k ih
    rw [zpow_add_one, pellNorm_mul d hd, ih, zpow_add_one₀ hne]
  · intro k ih
    rw [zpow_sub_one, pellNorm_mul d hd, ih, pellNorm_inv d hd, zpow_sub_one₀ hne]

/-- **The regulator scales linearly along *all* integer powers.** For `d ≥ 0`
and every `n : ℤ`, `R(aⁿ) = n · R(a)`: applying `log` to `pellNorm_zpow` and
using `Real.log_zpow` extends the parent's natural-number scaling law to the
whole exponent line. -/
theorem pellRegulator_zpow (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) (n : ℤ) :
    pellRegulator d (a ^ n) = (n : ℝ) * pellRegulator d a := by
  unfold pellRegulator
  rw [pellNorm_zpow d hd, Real.log_zpow]

/-- **The regulator of the inverse is the negative of the regulator**:
`R(a⁻¹) = −R(a)`. The `n = −1` instance of `pellRegulator_zpow`. -/
theorem pellRegulator_inv (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) :
    pellRegulator d a⁻¹ = -pellRegulator d a := by
  have h := pellRegulator_zpow d hd a (-1)
  simpa using h

/-- The regulator of a negative power: `R(a⁻ⁿ) = −n · R(a)` for `n : ℕ`. -/
theorem pellRegulator_zpow_neg (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) (n : ℕ) :
    pellRegulator d (a ^ (-(n : ℤ))) = -(n : ℝ) * pellRegulator d a := by
  rw [pellRegulator_zpow d hd]
  push_cast
  ring

end PellEquationOQ01OQ04OQ01
