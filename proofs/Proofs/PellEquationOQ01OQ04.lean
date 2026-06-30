import Mathlib

/-
# Pell Equation OQ-01-OQ-04: the Pell norm is a homomorphism, so the regulator is additive

The parent entry `pell-equation-oq-01` introduces, on Mathlib's group of Pell
solutions `Pell.Solution₁ d` (pairs `(x, y)` with `x² − d·y² = 1`), the **Pell
norm** and **regulator**

  `pellNorm d x y = x + y√d`,    `pellRegulator d a = log (pellNorm d a.x a.y)`,

and proves only a size bound (`1 ≤ pellNorm` for positive solutions). It leaves
open the *structural* question of how these interact with the group law — which
is the entire reason the regulator is the right invariant.

This entry supplies that structure. The Pell norm is a **multiplicative
homomorphism** from the solution group to `ℝˣ` (Brahmagupta's identity), so the
regulator is **additive**, and on powers it **scales linearly**:

* `pellNorm_one`        : `pellNorm` of the identity solution is `1`.
* `pellNorm_mul`        : **`pellNorm (a·b) = pellNorm a · pellNorm b`** (Brahmagupta).
* `pellNorm_mul_inv`    : `pellNorm a · pellNorm a⁻¹ = 1` — the conjugate identity
  `(x + y√d)(x − y√d) = x² − d·y² = 1`, exhibiting `pellNorm a⁻¹` as the inverse.
* `pellNorm_ne_zero`    : consequently `pellNorm a ≠ 0` for every solution.
* `pellRegulator_mul`   : **`R(a·b) = R(a) + R(b)`** — the regulator is additive.
* `pellNorm_pow` / `pellRegulator_pow` : `pellNorm (aⁿ) = (pellNorm a)ⁿ` and
  **`R(aⁿ) = n·R(a)`** — the regulator scales linearly along powers of a solution.

The last identity is exactly why a fundamental solution of regulator `R(D)`
generates a tower of solutions with regulators `R(D), 2R(D), 3R(D), …` — the
arithmetic backbone of the parent's regulator definition.

The engine is Brahmagupta composition `Pell.Solution₁.x_mul / y_mul` together
with `√d·√d = d` (needs `d ≥ 0`) and the defining relation `a.prop`.

`0` axioms.
-/

namespace PellEquationOQ01OQ04

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
`pellNorm (a·b) = pellNorm a · pellNorm b`: composing two Pell solutions
multiplies their norms `x + y√d`. -/
theorem pellNorm_mul (d : ℤ) (hd : 0 ≤ d) (a b : Solution₁ d) :
    pellNorm d (a * b).x (a * b).y = pellNorm d a.x a.y * pellNorm d b.x b.y := by
  simp only [pellNorm, Solution₁.x_mul, Solution₁.y_mul]
  have hsq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast hd)
  push_cast
  linear_combination (-((a.y : ℝ) * (b.y : ℝ))) * hsq

/-- **The conjugate identity.** `pellNorm a · pellNorm a⁻¹ = 1`, i.e.
`(x + y√d)(x − y√d) = x² − d·y² = 1`. Since `a⁻¹ = (x, −y)`, this exhibits the
norm of the inverse solution as the multiplicative inverse of the norm. -/
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

/-- **The regulator is additive.** For `d ≥ 0`, `R(a·b) = R(a) + R(b)`: the
logarithm turns norm multiplicativity into additivity of the regulator on the
solution group. -/
theorem pellRegulator_mul (d : ℤ) (hd : 0 ≤ d) (a b : Solution₁ d) :
    pellRegulator d (a * b) = pellRegulator d a + pellRegulator d b := by
  unfold pellRegulator
  rw [pellNorm_mul d hd, Real.log_mul (pellNorm_ne_zero d hd a) (pellNorm_ne_zero d hd b)]

/-- The norm of a power is the power of the norm: `pellNorm (aⁿ) = (pellNorm a)ⁿ`. -/
theorem pellNorm_pow (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) (n : ℕ) :
    pellNorm d (a ^ n).x (a ^ n).y = (pellNorm d a.x a.y) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact pellNorm_one d
  | succ n ih => rw [pow_succ, pellNorm_mul d hd, ih, pow_succ]

/-- **The regulator scales linearly along powers.** `R(aⁿ) = n·R(a)`. This is why
a fundamental solution of regulator `R(D)` generates solutions with regulators
`R(D), 2R(D), 3R(D), …`. -/
theorem pellRegulator_pow (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) (n : ℕ) :
    pellRegulator d (a ^ n) = (n : ℝ) * pellRegulator d a := by
  unfold pellRegulator
  rw [pellNorm_pow d hd, Real.log_pow]

end PellEquationOQ01OQ04
