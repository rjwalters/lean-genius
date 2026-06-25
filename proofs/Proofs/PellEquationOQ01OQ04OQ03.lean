import Mathlib

/-
# Pell Equation OQ-01-OQ-04-OQ-03: the norm as a `MonoidHom`, and the regulator as a minimal positive value

The grandparent `pell-equation-oq-01-oq-04` built the **Pell norm**
`pellNorm d x y = x + y√d` and proved its multiplicativity
(`pellNorm (a·b) = pellNorm a · pellNorm b`, Brahmagupta's identity) together with
the additivity of the **regulator** `R(a) = log‖a‖` on Mathlib's group of Pell
solutions `Pell.Solution₁ d`. The siblings `…-oq-01` / `…-oq-02` extended the
scaling law `R(aⁿ) = n·R(a)` across the whole integer exponent line and turned it
into a faithfulness/order statement (the regulator strictly orders the powers).

Those entries kept the homomorphism property as *bare lemmas*. This entry does two
genuinely new things.

## 1. Bundle the norm as an honest homomorphism

`pellNorm_one` and `pellNorm_mul` are exactly the axioms of a `MonoidHom`, so we
package them:

* `pellNormHom`        : `Solution₁ d →* ℝ`   — the norm as a monoid homomorphism into `(ℝ, ·)`.
* `pellNormUnitsHom`   : `Solution₁ d →* ℝˣ`  — since the norm is never zero, it lands in the
  multiplicative **group** of real units; this exhibits the solution group as mapping into `ℝˣ`.
* `pellRegulatorHom`   : `Solution₁ d →* Multiplicative ℝ` — the regulator as a group homomorphism
  into the additive group `(ℝ, +)` (the log of `pellNormUnitsHom`).

## 2. The regulator of a fundamental solution is the *minimal positive value*

Mathlib's `Pell.IsFundamental.eq_pow_of_nonneg` says every nonnegative solution is a
power `a = a₁ⁿ` of the fundamental solution `a₁`. Combined with `R(aⁿ) = n·R(a₁)`
and `R(a₁) > 0`, this yields the classical regulator characterisation:

* `pellRegulator_fundamental_pos` : `R(a₁) > 0` for a fundamental `a₁`.
* `pellRegulator_fundamental_le`  : every nontrivial positive solution `a` (`1 < a.x`, `0 < a.y`)
  has `R(a₁) ≤ R(a)` — the fundamental regulator is a lower bound.
* `pellRegulator_fundamental_lt`  : the bound is **strict** for `a ≠ a₁`.
* `isLeast_pellRegulator`          : `R(a₁)` is the **least element** of the set of regulators of
  nontrivial positive solutions — i.e. the regulator is literally the *minimal positive value*
  the regulator attains on the solution group.

The mathematical content of part 2 is the bridge from the multiplicative structure
theorem ("every solution is a power of `a₁`") to a metric extremality statement
("`a₁` minimises the regulator"): the additive scaling law converts "smallest
exponent `n ≥ 1`" into "smallest positive regulator `R(a₁)`".

The supporting norm/regulator lemmas (`pellNorm_one`, `pellNorm_mul`,
`pellNorm_mul_inv`, `pellNorm_ne_zero`, `pellRegulator_mul`, `pellNorm_pow`,
`pellRegulator_pow`) are restated here verbatim from the grandparent so the file is
self-contained; the genuinely new content is the bundled-homomorphism layer and the
`IsLeast` extremality theorem.

`0` axioms.
-/

namespace PellEquationOQ01OQ04OQ03

open Pell

/-- The Pell norm `x + y√d` (matching the grandparent definition). -/
noncomputable def pellNorm (d : ℤ) (x y : ℤ) : ℝ :=
  (x : ℝ) + (y : ℝ) * Real.sqrt (d : ℝ)

/-- The Pell regulator `log(x + y√d)` (matching the grandparent definition). -/
noncomputable def pellRegulator (d : ℤ) (a : Solution₁ d) : ℝ :=
  Real.log (pellNorm d a.x a.y)

variable {d : ℤ}

/-! ## Supporting norm/regulator lemmas (restated from the grandparent) -/

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

/-- The Pell norm is never zero. -/
theorem pellNorm_ne_zero (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) :
    pellNorm d a.x a.y ≠ 0 := by
  intro h
  have hkey := pellNorm_mul_inv d hd a
  rw [h, zero_mul] at hkey
  exact zero_ne_one hkey

/-- **The regulator is additive.** For `d ≥ 0`, `R(a·b) = R(a) + R(b)`. -/
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

/-- **The regulator scales linearly along powers.** `R(aⁿ) = n·R(a)`. -/
theorem pellRegulator_pow (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) (n : ℕ) :
    pellRegulator d (a ^ n) = (n : ℝ) * pellRegulator d a := by
  unfold pellRegulator
  rw [pellNorm_pow d hd, Real.log_pow]

/-! ## Part 1: the norm and regulator as bundled homomorphisms -/

/-- **The Pell norm as a `MonoidHom`.** For `d ≥ 0`, `pellNorm_one` and `pellNorm_mul`
are exactly the unit/multiplicativity axioms, so the norm bundles into an honest
homomorphism `Solution₁ d →* ℝ` from the solution group to the multiplicative monoid
of reals. -/
noncomputable def pellNormHom (d : ℤ) (hd : 0 ≤ d) : Solution₁ d →* ℝ where
  toFun a := pellNorm d a.x a.y
  map_one' := pellNorm_one d
  map_mul' := pellNorm_mul d hd

@[simp] theorem pellNormHom_apply (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) :
    pellNormHom d hd a = pellNorm d a.x a.y := rfl

/-- **The Pell norm as a homomorphism into the group of units `ℝˣ`.** Since the norm
is never zero (`pellNorm_ne_zero`), it factors through `ℝˣ`, exhibiting the Pell
solution group as mapping into the multiplicative *group* of real units rather than
merely the monoid. -/
noncomputable def pellNormUnitsHom (d : ℤ) (hd : 0 ≤ d) : Solution₁ d →* ℝˣ where
  toFun a := Units.mk0 (pellNorm d a.x a.y) (pellNorm_ne_zero d hd a)
  map_one' := by ext; simpa using pellNorm_one d
  map_mul' a b := by ext; simpa using pellNorm_mul d hd a b

@[simp] theorem pellNormUnitsHom_val (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) :
    (pellNormUnitsHom d hd a : ℝ) = pellNorm d a.x a.y := rfl

/-- **The regulator as a group homomorphism into `(ℝ, +)`.** Packaging `R(1) = 0`
and `R(a·b) = R(a) + R(b)` as a `MonoidHom` into `Multiplicative ℝ` (the additive
group of reals viewed multiplicatively). -/
noncomputable def pellRegulatorHom (d : ℤ) (hd : 0 ≤ d) :
    Solution₁ d →* Multiplicative ℝ where
  toFun a := Multiplicative.ofAdd (pellRegulator d a)
  map_one' := by
    show Multiplicative.ofAdd (pellRegulator d (1 : Solution₁ d)) = 1
    rw [show (1 : Multiplicative ℝ) = Multiplicative.ofAdd (0 : ℝ) from rfl]
    congr 1
    unfold pellRegulator
    rw [pellNorm_one d, Real.log_one]
  map_mul' a b := by
    show Multiplicative.ofAdd (pellRegulator d (a * b))
      = Multiplicative.ofAdd (pellRegulator d a) * Multiplicative.ofAdd (pellRegulator d b)
    rw [pellRegulator_mul d hd, ← ofAdd_add]

@[simp] theorem pellRegulatorHom_apply (d : ℤ) (hd : 0 ≤ d) (a : Solution₁ d) :
    Multiplicative.toAdd (pellRegulatorHom d hd a) = pellRegulator d a := rfl

/-! ## Part 2: the regulator as a minimal positive value -/

/-- A nontrivial positive solution (`1 < a.x`, `0 < a.y`, with `d > 0`) has norm
strictly greater than `1`: `x + y√d > 1`. -/
theorem one_lt_pellNorm {a : Solution₁ d} (hd : 0 < d) (hx : 1 < a.x) (hy : 0 < a.y) :
    1 < pellNorm d a.x a.y := by
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hxr : (1 : ℝ) < (a.x : ℝ) := by exact_mod_cast hx
  have hyr : (0 : ℝ) < (a.y : ℝ) := by exact_mod_cast hy
  have hpos : 0 < (a.y : ℝ) * Real.sqrt (d : ℝ) := mul_pos hyr hsqrt
  simp only [pellNorm]
  linarith

/-- **The regulator of a fundamental solution is strictly positive.** -/
theorem pellRegulator_fundamental_pos {a₁ : Solution₁ d} (h : IsFundamental a₁) :
    0 < pellRegulator d a₁ := by
  unfold pellRegulator
  exact Real.log_pos (one_lt_pellNorm h.d_pos h.1 h.2.1)

/-- **Lower bound / minimality.** For a fundamental solution `a₁`, every nontrivial
positive solution `a` (`1 < a.x`, `0 < a.y`) satisfies `R(a₁) ≤ R(a)`. The proof
writes `a = a₁ⁿ` with `n ≥ 1` and uses `R(a₁ⁿ) = n·R(a₁) ≥ R(a₁)`. -/
theorem pellRegulator_fundamental_le {a₁ : Solution₁ d} (h : IsFundamental a₁)
    {a : Solution₁ d} (hx : 1 < a.x) (hy : 0 < a.y) :
    pellRegulator d a₁ ≤ pellRegulator d a := by
  obtain ⟨n, rfl⟩ := h.eq_pow_of_nonneg (zero_lt_one.trans hx) hy.le
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero, Solution₁.x_one] at hx; exact absurd hx (lt_irrefl 1)
    · exact_mod_cast h0
  rw [pellRegulator_pow d h.d_pos.le]
  have hR : 0 < pellRegulator d a₁ := pellRegulator_fundamental_pos h
  calc pellRegulator d a₁ = 1 * pellRegulator d a₁ := (one_mul _).symm
    _ ≤ (n : ℝ) * pellRegulator d a₁ := mul_le_mul_of_nonneg_right hn1 hR.le

/-- **Strict minimality.** The fundamental solution is the *unique* minimiser: any
nontrivial positive solution `a ≠ a₁` has `R(a₁) < R(a)` (here `a = a₁ⁿ` with `n ≥ 2`). -/
theorem pellRegulator_fundamental_lt {a₁ : Solution₁ d} (h : IsFundamental a₁)
    {a : Solution₁ d} (hx : 1 < a.x) (hy : 0 < a.y) (hne : a ≠ a₁) :
    pellRegulator d a₁ < pellRegulator d a := by
  obtain ⟨n, rfl⟩ := h.eq_pow_of_nonneg (zero_lt_one.trans hx) hy.le
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by
    match n, hx, hne with
    | 0, hx, _ => rw [pow_zero, Solution₁.x_one] at hx; exact absurd hx (lt_irrefl 1)
    | 1, _, hne => exact absurd (pow_one a₁) hne
    | (k + 2), _, _ => exact_mod_cast Nat.le_add_left 2 k
  rw [pellRegulator_pow d h.d_pos.le]
  have hR : 0 < pellRegulator d a₁ := pellRegulator_fundamental_pos h
  calc pellRegulator d a₁ = 1 * pellRegulator d a₁ := (one_mul _).symm
    _ < (n : ℝ) * pellRegulator d a₁ :=
        mul_lt_mul_of_pos_right (by linarith) hR

/-- **The regulator is the minimal positive value.** For a fundamental solution `a₁`,
`R(a₁)` is the *least element* of the set of regulators of all nontrivial positive
Pell solutions. This is the classical statement that the regulator (the period of the
fundamental unit) is the smallest positive value attained by `log‖a‖` on the solution
group. -/
theorem isLeast_pellRegulator {a₁ : Solution₁ d} (h : IsFundamental a₁) :
    IsLeast {r : ℝ | ∃ a : Solution₁ d, 1 < a.x ∧ 0 < a.y ∧ r = pellRegulator d a}
            (pellRegulator d a₁) := by
  constructor
  · exact ⟨a₁, h.1, h.2.1, rfl⟩
  · rintro r ⟨a, hax, hay, rfl⟩
    exact pellRegulator_fundamental_le h hax hay

/-- The minimal value is itself positive: the least regulator over nontrivial positive
solutions is `> 0`. -/
theorem isLeast_pellRegulator_pos {a₁ : Solution₁ d} (h : IsFundamental a₁) :
    0 < (pellRegulator d a₁) := pellRegulator_fundamental_pos h

end PellEquationOQ01OQ04OQ03
