import Mathlib

/-
# Pell Equation OQ-01-OQ-04-OQ-02: the regulator faithfully orders the powers

The grandparent `pell-equation-oq-01-oq-04` built the **Pell norm**
`pellNorm d x y = x + y√d` as a multiplicative homomorphism on Mathlib's group of
Pell solutions `Pell.Solution₁ d`, and the parent `pell-equation-oq-01-oq-04-oq-01`
extended the scaling law `R(aⁿ) = n · R(a)` (where `R = pellRegulator`) across the
*entire* integer exponent line `n : ℤ`.

This entry turns that linear scaling law into a **faithfulness / order** statement.
Write `‖a‖ = pellNorm d a.x a.y` for the real embedding `x + y√d` of a solution.
The only obstruction to `a` having infinite order is `‖a‖ = 1`; as soon as
`‖a‖ > 1` the real-analytic regulator `R(a) = log‖a‖` is *strictly positive*, and
since `R(aⁿ) = n · R(a)` is then a strictly increasing `ℤ`-linear ruler, the powers
`aⁿ` are pairwise distinct and `a` has infinite order. Concretely:

* `pellRegulator_one`              : `R(1) = 0` — the identity sits at the origin of the ruler.
* `pellRegulator_pos`              : `‖a‖ > 1 ⟹ R(a) > 0` (`Real.log_pos`).
* `pellRegulator_zpow_strictMono`  : `‖a‖ > 1 ⟹ n ↦ R(aⁿ)` is **strictly monotone** —
  the regulator faithfully (and order-preservingly) labels the integer powers.
* `zpow_injective`                 : `‖a‖ > 1 ⟹ n ↦ aⁿ` is **injective** — no two
  distinct integer powers coincide.
* `orderOf_eq_zero`                 : `‖a‖ > 1 ⟹ orderOf a = 0` — `a` has **infinite order**.
* `not_isOfFinOrder`               : the same fact phrased as `¬ IsOfFinOrder a`.

The mathematical content is the bridge from the *additive* group `(ℤ, +)` of
exponents to the *ordered* additive group `(ℝ, +, <)` via the strictly positive
regulator: `R(a) > 0` is exactly the hypothesis that makes `n ↦ n · R(a)` an
order embedding, and strict monotonicity of an order embedding is what forbids
finite order. Everything downstream of `pellRegulator_pos` is pure order theory —
no further Pell-specific computation is needed, because the algebra of
`pellNorm_zpow` / `pellRegulator_zpow` is already done.

The supporting norm/regulator lemmas (`pellNorm_one`, `pellNorm_mul`,
`pellNorm_mul_inv`, `pellNorm_ne_zero`, `pellNorm_inv`, `pellNorm_zpow`,
`pellRegulator_zpow`) are restated here verbatim from the parent so the file is
self-contained; the genuinely new content is the order/faithfulness layer.

`0` axioms.
-/

namespace PellEquationOQ01OQ04OQ02

open Pell

/-- The Pell norm `x + y√d` (matching the grandparent definition). -/
noncomputable def pellNorm (d : ℤ) (x y : ℤ) : ℝ :=
  (x : ℝ) + (y : ℝ) * Real.sqrt (d : ℝ)

/-- The Pell regulator `log(x + y√d)` (matching the grandparent definition). -/
noncomputable def pellRegulator (d : ℤ) (a : Solution₁ d) : ℝ :=
  Real.log (pellNorm d a.x a.y)

variable {d : ℤ}

/-- The norm of the identity solution `(1, 0)` is `1`. -/
theorem pellNorm_one (d : ℤ) :
    pellNorm d (1 : Solution₁ d).x (1 : Solution₁ d).y = 1 := by
  rw [Solution₁.x_one, Solution₁.y_one]
  simp [pellNorm]

/-- **Brahmagupta's identity / norm multiplicativity** (parent). -/
theorem pellNorm_mul (d : ℤ) (hd : 0 ≤ d) (a b : Solution₁ d) :
    pellNorm d (a * b).x (a * b).y = pellNorm d a.x a.y * pellNorm d b.x b.y := by
  simp only [pellNorm, Solution₁.x_mul, Solution₁.y_mul]
  have hsq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast hd)
  push_cast
  linear_combination (-((a.y : ℝ) * (b.y : ℝ))) * hsq

/-- **The conjugate identity** (parent): `pellNorm a · pellNorm a⁻¹ = 1`. -/
theorem pellNorm_mul_inv (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) :
    pellNorm d a.x a.y * pellNorm d a⁻¹.x a⁻¹.y = 1 := by
  rw [Solution₁.x_inv, Solution₁.y_inv]
  simp only [pellNorm]
  have hsq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt (by exact_mod_cast hd)
  have hprop : (a.x : ℝ) ^ 2 - (d : ℝ) * (a.y : ℝ) ^ 2 = 1 := by exact_mod_cast a.prop
  push_cast
  linear_combination hprop - ((a.y : ℝ) ^ 2) * hsq

/-- The Pell norm is never zero (parent). -/
theorem pellNorm_ne_zero (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) :
    pellNorm d a.x a.y ≠ 0 := by
  intro h
  have hkey := pellNorm_mul_inv d hd a
  rw [h, zero_mul] at hkey
  exact zero_ne_one hkey

/-- **The norm of the inverse is the reciprocal of the norm** (parent). -/
theorem pellNorm_inv (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) :
    pellNorm d a⁻¹.x a⁻¹.y = (pellNorm d a.x a.y)⁻¹ := by
  have hkey := pellNorm_mul_inv d hd a
  have hne := pellNorm_ne_zero d hd a
  have h1 : pellNorm d a⁻¹.x a⁻¹.y = 1 / pellNorm d a.x a.y := by
    rw [eq_div_iff hne, mul_comm]; exact hkey
  rw [h1, one_div]

/-- **The Pell norm intertwines integer powers with real `zpow`** (parent):
`pellNorm (aⁿ) = (pellNorm a)ⁿ` for every `n : ℤ`. -/
theorem pellNorm_zpow (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) (n : ℤ) :
    pellNorm d (a ^ n).x (a ^ n).y = (pellNorm d a.x a.y) ^ n := by
  have hne : pellNorm d a.x a.y ≠ 0 := pellNorm_ne_zero d hd a
  refine Int.induction_on n ?_ ?_ ?_
  · simp [pellNorm]
  · intro k ih
    rw [zpow_add_one, pellNorm_mul d hd, ih, zpow_add_one₀ hne]
  · intro k ih
    rw [zpow_sub_one, pellNorm_mul d hd, ih, pellNorm_inv d hd, zpow_sub_one₀ hne]

/-- **The regulator scales linearly along all integer powers** (parent):
`R(aⁿ) = n · R(a)` for every `n : ℤ`. -/
theorem pellRegulator_zpow (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) (n : ℤ) :
    pellRegulator d (a ^ n) = (n : ℝ) * pellRegulator d a := by
  unfold pellRegulator
  rw [pellNorm_zpow d hd, Real.log_zpow]

/-! ## New content: the order / faithfulness layer -/

/-- **The identity solution sits at the origin of the regulator ruler:** `R(1) = 0`.
The norm of `(1, 0)` is `1` and `log 1 = 0`. -/
theorem pellRegulator_one (d : ℤ) : pellRegulator d (1 : Solution₁ d) = 0 := by
  unfold pellRegulator
  rw [pellNorm_one d, Real.log_one]

/-- **A solution lying strictly beyond `1` has strictly positive regulator.**
If the real embedding `‖a‖ = x + y√d` exceeds `1` then `R(a) = log‖a‖ > 0`. This is
the single inequality that powers every faithfulness statement below. -/
theorem pellRegulator_pos (d : ℤ) (a : Solution₁ d)
    (h : 1 < pellNorm d a.x a.y) : 0 < pellRegulator d a :=
  Real.log_pos h

/-- **The regulator strictly monotonically orders the integer powers.** For `d ≥ 0`
and `‖a‖ > 1`, the map `n ↦ R(aⁿ)` is strictly increasing in `n : ℤ`. Because
`R(aⁿ) = n · R(a)` with `R(a) > 0`, this is just the fact that scaling by a positive
real preserves strict order. The regulator is thus a faithful, order-preserving
ruler for the cyclic subgroup generated by `a`. -/
theorem pellRegulator_zpow_strictMono (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d)
    (h : 1 < pellNorm d a.x a.y) :
    StrictMono (fun n : ℤ => pellRegulator d (a ^ n)) := by
  have hpos := pellRegulator_pos d a h
  intro m n hmn
  simp only [pellRegulator_zpow d hd]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hmn) hpos

/-- **Faithfulness: distinct exponents give distinct powers.** For `d ≥ 0` and
`‖a‖ > 1`, the map `n ↦ aⁿ` from `ℤ` into `Solution₁ d` is injective. If `aᵐ = aⁿ`
then their regulators agree, and strict monotonicity of `n ↦ R(aⁿ)` forces `m = n`. -/
theorem zpow_injective (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d)
    (h : 1 < pellNorm d a.x a.y) :
    Function.Injective (fun n : ℤ => a ^ n) := by
  intro m n hmn
  exact (pellRegulator_zpow_strictMono d hd a h).injective
    (congrArg (pellRegulator d) hmn)

/-- **A Pell solution beyond `1` has infinite order.** For `d ≥ 0`, if `‖a‖ > 1`
then `orderOf a = 0`. Were some positive power `aⁿ = 1`, applying the regulator
would give `0 = R(1) = R(aⁿ) = n · R(a)` with both `n > 0` and `R(a) > 0` — a
contradiction. -/
theorem orderOf_eq_zero (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d)
    (h : 1 < pellNorm d a.x a.y) : orderOf a = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn heq
  have hpos := pellRegulator_pos d a h
  have hR : pellRegulator d (a ^ (n : ℤ)) = (n : ℝ) * pellRegulator d a :=
    pellRegulator_zpow d hd a n
  rw [zpow_natCast, heq, pellRegulator_one] at hR
  have hpos2 : (0 : ℝ) < (n : ℝ) * pellRegulator d a :=
    mul_pos (by exact_mod_cast hn) hpos
  rw [← hR] at hpos2
  exact lt_irrefl 0 hpos2

/-- **`¬ IsOfFinOrder a`** — the order-zero fact restated through Mathlib's
finite-order predicate. -/
theorem not_isOfFinOrder (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d)
    (h : 1 < pellNorm d a.x a.y) : ¬ IsOfFinOrder a := by
  rw [← orderOf_eq_zero_iff]
  exact orderOf_eq_zero d hd a h

end PellEquationOQ01OQ04OQ02
