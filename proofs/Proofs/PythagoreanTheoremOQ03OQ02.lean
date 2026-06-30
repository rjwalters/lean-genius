/-
# Relativistic Velocity Addition from Rapidity (Pythagorean OQ-03-OQ-02)

The parent gallery entry **pythagorean-theorem-oq-03** ("Pythagorean Theorem in
Non-Euclidean Geometry") develops the Minkowski branch τ² = t² − x²: Lorentz
boosts parameterized by rapidity φ (with β = tanh φ), interval invariance, and
the *additivity of rapidity* under composition of boosts (φ₁, φ₂ ↦ φ₁ + φ₂).
Its open questions explicitly ask to

  > formalize the rapidity–velocity relation β = tanh(φ) and derive relativistic
  > velocity addition.

This file answers that. The velocity associated to rapidity φ is β = tanh φ, and
the additivity of rapidity becomes the **relativistic velocity-addition law**

    β = (β₁ + β₂) / (1 + β₁ β₂),   i.e.   tanh(φ₁ + φ₂) = velAdd (tanh φ₁) (tanh φ₂).

We prove, with zero axioms (imports Mathlib only):

  * `tanh_lt_one` / `neg_one_lt_tanh` / `abs_tanh_lt_one` — every rapidity gives a
    strictly subluminal speed |β| < 1;
  * `tanh_add` — rapidity additivity *is* the velocity-addition formula;
  * `abs_velAdd_lt_one` — **closure**: composing two subluminal velocities stays
    subluminal (c is never exceeded), proved algebraically via
    1 ∓ velAdd = (1 ∓ β₁)(1 ∓ β₂)/(1 + β₁ β₂);
  * `velAdd_one` — **light-speed invariance**: adding any velocity to c gives c;
  * `velAdd_sub_sum` — the **Galilean limit**: the correction to β₁ + β₂ is the
    second-order term −(β₁+β₂)β₁β₂/(1+β₁β₂);
  * `cosh_sq_eq_inv_one_sub_tanh_sq` — the **Lorentz factor** γ = cosh φ obeys
    γ² = 1/(1 − β²);
  * concrete checks: ½c ⊕ ½c = ⅘ c, and ⅗c ⊕ c = c.

Self-contained: the rapidity/velocity facts are derived directly from Mathlib's
`Real.sinh`/`Real.cosh`/`Real.tanh`, so nothing is imported from the parent.
-/
import Mathlib

open Real

namespace PythagoreanTheoremOQ03OQ02

/- ## Speeds from rapidities are subluminal: |tanh φ| < 1 -/

/-- A rapidity never reaches the speed of light from above: `tanh φ < 1`.
Equivalent to `sinh φ < cosh φ`, i.e. `0 < cosh φ − sinh φ = exp(−φ)`. -/
theorem tanh_lt_one (x : ℝ) : Real.tanh x < 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_lt_one (Real.cosh_pos x)]
  have h := Real.cosh_sub_sinh x
  have := Real.exp_pos (-x)
  linarith

/-- A rapidity never reaches the speed of light from below: `-1 < tanh φ`.
Equivalent to `-cosh φ < sinh φ`, i.e. `0 < cosh φ + sinh φ = exp(φ)`. -/
theorem neg_one_lt_tanh (x : ℝ) : -1 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh, lt_div_iff₀ (Real.cosh_pos x)]
  have h : Real.cosh x + Real.sinh x = Real.exp x := by
    have := Real.cosh_sub_sinh (-x)
    rw [Real.cosh_neg, Real.sinh_neg, neg_neg] at this
    linarith
  have := Real.exp_pos x
  linarith

/-- The speed associated to any rapidity is strictly subluminal: `|tanh φ| < 1`. -/
theorem abs_tanh_lt_one (x : ℝ) : |Real.tanh x| < 1 :=
  abs_lt.mpr ⟨neg_one_lt_tanh x, tanh_lt_one x⟩

/- ## Relativistic velocity addition -/

/-- The relativistic velocity-addition operation `β₁ ⊕ β₂ = (β₁+β₂)/(1+β₁β₂)`. -/
noncomputable def velAdd (β₁ β₂ : ℝ) : ℝ := (β₁ + β₂) / (1 + β₁ * β₂)

/-- The relativistic denominator stays positive for any two subluminal speeds:
`(1+β₁)(1+β₂) > 0` and `(1-β₁)(1-β₂) > 0` sum to `2(1 + β₁β₂) > 0`. -/
theorem one_add_mul_pos {β₁ β₂ : ℝ} (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    0 < 1 + β₁ * β₂ := by
  rw [abs_lt] at h₁ h₂
  nlinarith [mul_pos (by linarith : (0:ℝ) < 1 + β₁) (by linarith : (0:ℝ) < 1 + β₂),
    mul_pos (by linarith : (0:ℝ) < 1 - β₁) (by linarith : (0:ℝ) < 1 - β₂)]

/-- The relativistic denominator `1 + tanh φ₁ tanh φ₂` is positive — immediate from
`|tanh φ| < 1`. -/
theorem one_add_tanh_mul_pos (x y : ℝ) : 0 < 1 + Real.tanh x * Real.tanh y :=
  one_add_mul_pos (abs_tanh_lt_one x) (abs_tanh_lt_one y)

/-- The "cleared" form of velocity addition: multiplying through by the
denominator. Keeping `sinh(φ₁+φ₂)`/`cosh(φ₁+φ₂)` atomic lets `field_simp` clear the
(product) denominators `cosh φᵢ`; the addition formulas then close it by `ring`. -/
theorem tanh_add_mul (x y : ℝ) :
    Real.tanh (x + y) * (1 + Real.tanh x * Real.tanh y) = Real.tanh x + Real.tanh y := by
  have hx := (Real.cosh_pos x).ne'
  have hy := (Real.cosh_pos y).ne'
  have hxy := (Real.cosh_pos (x + y)).ne'
  rw [Real.tanh_eq_sinh_div_cosh x, Real.tanh_eq_sinh_div_cosh y,
    Real.tanh_eq_sinh_div_cosh (x + y)]
  field_simp
  rw [Real.sinh_add, Real.cosh_add]
  ring

/-- **Relativistic velocity addition is rapidity addition.** The velocity of the
composite boost with rapidity `φ₁ + φ₂` is `velAdd` of the two velocities:

    tanh(φ₁ + φ₂) = (tanh φ₁ + tanh φ₂) / (1 + tanh φ₁ tanh φ₂). -/
theorem tanh_add (x y : ℝ) :
    Real.tanh (x + y) = velAdd (Real.tanh x) (Real.tanh y) := by
  unfold velAdd
  rw [eq_div_iff (one_add_tanh_mul_pos x y).ne']
  exact tanh_add_mul x y

/- ## Closure: subluminal ⊕ subluminal = subluminal -/

/-- **The speed of light is never exceeded.** Composing two strictly subluminal
velocities yields a strictly subluminal velocity: `|velAdd β₁ β₂| < 1`. The proof
is the algebraic identity `1 ∓ velAdd = (1 ∓ β₁)(1 ∓ β₂)/(1 + β₁ β₂)`. -/
theorem abs_velAdd_lt_one {β₁ β₂ : ℝ} (h₁ : |β₁| < 1) (h₂ : |β₂| < 1) :
    |velAdd β₁ β₂| < 1 := by
  have hd := one_add_mul_pos h₁ h₂
  rw [abs_lt] at h₁ h₂ ⊢
  refine ⟨?_, ?_⟩
  · -- -1 < velAdd β₁ β₂  ⟺  0 < (1+β₁)(1+β₂)
    unfold velAdd
    rw [lt_div_iff₀ hd]
    nlinarith [mul_pos (by linarith : (0:ℝ) < 1 + β₁) (by linarith : (0:ℝ) < 1 + β₂)]
  · -- velAdd β₁ β₂ < 1  ⟺  0 < (1-β₁)(1-β₂)
    unfold velAdd
    rw [div_lt_one hd]
    nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - β₁) (by linarith : (0:ℝ) < 1 - β₂)]

/-- **Closure for rapidities, stated directly**: any two rapidity-velocities
compose to a subluminal velocity, equal to the velocity of the summed rapidity. -/
theorem velAdd_tanh_subluminal (x y : ℝ) :
    velAdd (Real.tanh x) (Real.tanh y) = Real.tanh (x + y) ∧
      |velAdd (Real.tanh x) (Real.tanh y)| < 1 :=
  ⟨(tanh_add x y).symm, by rw [← tanh_add]; exact abs_tanh_lt_one _⟩

/- ## Light-speed invariance -/

/-- **The speed of light is invariant.** Adding any velocity `β ≠ -1` to `c` (the
speed `1`) returns `c`: `velAdd β 1 = 1`. -/
theorem velAdd_one (β : ℝ) (hβ : β ≠ -1) : velAdd β 1 = 1 := by
  unfold velAdd
  have hne : (1 : ℝ) + β * 1 ≠ 0 := by
    rw [mul_one]; intro h; exact hβ (by linarith)
  rw [div_eq_one_iff_eq hne]; ring

/-- Symmetric form: adding `c` to any velocity `β ≠ -1` returns `c`. -/
theorem one_velAdd (β : ℝ) (hβ : β ≠ -1) : velAdd 1 β = 1 := by
  unfold velAdd
  have hne : (1 : ℝ) + 1 * β ≠ 0 := by
    rw [one_mul]; intro h; exact hβ (by linarith)
  rw [div_eq_one_iff_eq hne]; ring

/- ## Galilean (non-relativistic) limit -/

/-- **The classical limit.** Velocity addition differs from the Galilean sum
`β₁ + β₂` only by the second-order term `−(β₁+β₂)β₁β₂/(1+β₁β₂)`, which vanishes
when `β₁β₂` is negligible — recovering Galilean addition at low speeds. -/
theorem velAdd_sub_sum (β₁ β₂ : ℝ) (hd : 1 + β₁ * β₂ ≠ 0) :
    velAdd β₁ β₂ - (β₁ + β₂) = -(β₁ + β₂) * (β₁ * β₂) / (1 + β₁ * β₂) := by
  unfold velAdd
  field_simp
  ring

/- ## The Lorentz factor -/

/-- The identity `1 − tanh²φ = 1/cosh²φ`, from `cosh²φ − sinh²φ = 1`. -/
theorem one_sub_tanh_sq (x : ℝ) : 1 - Real.tanh x ^ 2 = 1 / Real.cosh x ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_pow]
  have hc := (Real.cosh_pos x).ne'
  have h := Real.cosh_sq_sub_sinh_sq x
  field_simp
  linarith

/-- **The Lorentz factor** `γ = cosh φ` satisfies the familiar `γ² = 1/(1 − β²)`,
with `β = tanh φ` the velocity. -/
theorem cosh_sq_eq_inv_one_sub_tanh_sq (x : ℝ) :
    Real.cosh x ^ 2 = 1 / (1 - Real.tanh x ^ 2) := by
  rw [one_sub_tanh_sq, one_div_one_div]

/- ## Concrete instances -/

/-- Half the speed of light added to half the speed of light gives `⅘ c`, not `c`:
`velAdd (1/2) (1/2) = 4/5`. -/
theorem velAdd_half_half : velAdd (1 / 2) (1 / 2) = 4 / 5 := by
  unfold velAdd; norm_num

/-- `⅗ c` added to `c` is `c` — light-speed invariance in a concrete instance. -/
theorem velAdd_three_fifths_one : velAdd (3 / 5) 1 = 1 := by
  unfold velAdd; norm_num

end PythagoreanTheoremOQ03OQ02
