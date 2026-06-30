import Mathlib

/-
# Gelfond–Schneider — OQ-01: Baker's Theorem Proves Strictly More — Transcendence of Linear Forms in Two Logarithms

## Research Problem: gelfond-schneider-oq-01

> *Can Baker's theorem be used to prove more transcendence results?*

The gallery parent (`gelfond-schneider`) records the Gelfond–Schneider theorem (Hilbert's 7th
problem) as a stated assumption.  Gelfond–Schneider, and its sibling Hermite–Lindemann, are both
**single-logarithm** statements: they control one quantity of the shape `b · log a` (equivalently
one power `a ^ b = exp(b · log a)`).  In 1966 Alan Baker proved the decisive generalisation to
**several** logarithms — *linear forms in logarithms* — for which he received the Fields Medal.

This file answers OQ-01 in the affirmative by formalising the two-logarithm case of Baker's
theorem and deriving a concrete transcendence result that the single-logarithm theory does
**not** reach:

> **`log 2 + √2 · log 3` is transcendental.**

## Why this is genuinely beyond Gelfond–Schneider / Lindemann

* Hermite–Lindemann gives transcendence of a *single* `log a` (e.g. `log 2`, `log 3` are each
  transcendental), and an algebraic multiple of one transcendental is trivially transcendental.
* The new phenomenon is the **sum** `β₁ log a₁ + β₂ log a₂` of two `ℚ`-linearly-independent
  logarithms with algebraic coefficients: a priori the two transcendentals could cancel into an
  algebraic number.  Baker's theorem is exactly the statement that they cannot — the form is
  transcendental whenever the coefficients are not both zero.  Gelfond–Schneider (`n = 1`) says
  nothing about this `n = 2` cancellation question.

## Main results

* `baker_linear_form_two` — Baker's theorem, two-logarithm homogeneous form, stated as an
  `axiom` exactly as the parent entry states Gelfond–Schneider.  For algebraic bases `a₁, a₂ > 1`
  with `ℚ`-linearly independent logarithms (`log a₁ / log a₂` irrational) and algebraic
  coefficients `β₁, β₂` not both zero, the linear form `β₁ log a₁ + β₂ log a₂` is transcendental.
* `irrational_log_three_div_log_two`, `irrational_log_two_div_log_three` — the independence input
  for the bases `2, 3`, via the classical parity argument `2^p = 3^d ⇒ 2 ∣ 3`.
* `sqrt_two_algebraic` — `√2` is algebraic (root of `X² − 2`), the algebraic-coefficient input.
* `transcendental_log_two_add_sqrt_two_log_three` — the flagship consequence:
  `log 2 + √2 · log 3` is transcendental.
* `transcendental_log_six` — sanity sibling: the *collapsing* case `log 2 + log 3 = log 6`
  recovered as a single-logarithm transcendence (here `n = 2` Baker agrees with Lindemann).

## Assumption

`baker_linear_form_two` is the sole non-foundational assumption, mirroring the parent's
treatment of Gelfond–Schneider: the full proof of Baker's theorem (Baker's auxiliary functions,
zero estimates, and the theory of linear forms in logarithms) is not formalised.  Every theorem
below is otherwise fully machine-checked; `#print axioms` shows the only non-foundational
dependency is this single Baker assumption.

Tags: transcendental-number-theory, baker-theorem, linear-forms-in-logarithms, gelfond-schneider,
hilbert-7, logarithm
-/

namespace GelfondSchneiderOQ01

open Polynomial Real

/-- **Baker's theorem** (linear forms in logarithms, two-logarithm homogeneous form), stated as
    an assumption in the same spirit as the gallery parent states Gelfond–Schneider.

    If `a₁, a₂ > 1` are algebraic and their logarithms are linearly independent over `ℚ` (encoded
    as `log a₁ / log a₂ ∉ ℚ`), then for any algebraic coefficients `β₁, β₂` not both zero, the
    linear form `β₁ · log a₁ + β₂ · log a₂` is transcendental.

    This is the `n = 2` case of Baker's 1966 theorem; the `n = 1` analogue is Gelfond–Schneider /
    Hermite–Lindemann. -/
axiom baker_linear_form_two
    (a₁ a₂ : ℝ) (ha₁ : 1 < a₁) (ha₂ : 1 < a₂)
    (halg₁ : IsAlgebraic ℚ a₁) (halg₂ : IsAlgebraic ℚ a₂)
    (hindep : Irrational (Real.log a₁ / Real.log a₂))
    (β₁ β₂ : ℝ) (hβ₁ : IsAlgebraic ℚ β₁) (hβ₂ : IsAlgebraic ℚ β₂)
    (hβ_ne : ¬ (β₁ = 0 ∧ β₂ = 0)) :
    Transcendental ℚ (β₁ * Real.log a₁ + β₂ * Real.log a₂)

/-- Every rational, viewed in `ℝ`, is algebraic — supplies the algebraic bases `2, 3`. -/
private lemma rat_cast_algebraic (q : ℚ) : IsAlgebraic ℚ ((q : ℝ)) := by
  refine ⟨X - C q, ?_, ?_⟩
  · intro h
    have hcoeff : (X - C q : ℚ[X]).coeff 1 = 0 := by rw [h]; simp
    simp at hcoeff
  · simp

/-- `(2 : ℝ)` is algebraic over `ℚ`. -/
private lemma two_algebraic : IsAlgebraic ℚ ((2 : ℝ)) := by
  have := rat_cast_algebraic 2
  simpa using this

/-- `(3 : ℝ)` is algebraic over `ℚ`. -/
private lemma three_algebraic : IsAlgebraic ℚ ((3 : ℝ)) := by
  have := rat_cast_algebraic 3
  simpa using this

/-- `(1 : ℝ)` is algebraic over `ℚ`. -/
private lemma one_algebraic : IsAlgebraic ℚ ((1 : ℝ)) := by
  have := rat_cast_algebraic 1
  simpa using this

/-- `√2` is algebraic over `ℚ` (a root of `X² − 2`) — supplies the algebraic coefficient. -/
lemma sqrt_two_algebraic : IsAlgebraic ℚ (Real.sqrt 2) := by
  refine ⟨X ^ 2 - C 2, ?_, ?_⟩
  · intro h
    have hcoeff : (X ^ 2 - C 2 : ℚ[X]).coeff 2 = 0 := by rw [h]; simp
    simp at hcoeff
  · simp [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **`log 3 / log 2` is irrational.**  A rational value `p/d` exponentiates to `2^p = 3^d` for
    positive integers `p, d`, impossible by parity (`2 ∣ 3^d ⇒ 2 ∣ 3`). -/
theorem irrational_log_three_div_log_two : Irrational (Real.log 3 / Real.log 2) := by
  rw [Irrational]
  rintro ⟨q, hq⟩
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hqpos : (0 : ℝ) < (q : ℝ) := by rw [hq]; positivity
  have hqnum_pos : 0 < q.num := by
    rwa [Rat.num_pos, ← Rat.cast_pos (K := ℝ)]
  have hden : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.pos
  have hcross : (q.num : ℝ) * Real.log 2 = (q.den : ℝ) * Real.log 3 := by
    have hqeq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by exact_mod_cast (Rat.num_div_den q).symm
    rw [hqeq] at hq
    field_simp at hq
    nlinarith [hq, hl2, hl3]
  set N : ℕ := q.num.toNat with hN
  have hNcast : (N : ℝ) = (q.num : ℝ) := by
    rw [hN]; exact_mod_cast Int.toNat_of_nonneg (le_of_lt hqnum_pos)
  have hNpos : 0 < N := by rw [hN]; omega
  have hlog : Real.log ((2 : ℝ) ^ N) = Real.log ((3 : ℝ) ^ q.den) := by
    rw [Real.log_pow, Real.log_pow, hNcast]
    linarith [hcross]
  have hpow : (2 : ℝ) ^ N = (3 : ℝ) ^ q.den := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    have h3 : (0 : ℝ) < (3 : ℝ) ^ q.den := by positivity
    have := congrArg Real.exp hlog
    rwa [Real.exp_log h2, Real.exp_log h3] at this
  have hnat : (2 : ℕ) ^ N = (3 : ℕ) ^ q.den := by
    have : ((2 ^ N : ℕ) : ℝ) = ((3 ^ q.den : ℕ) : ℝ) := by push_cast; exact hpow
    exact_mod_cast this
  have hdvd : (2 : ℕ) ∣ 3 ^ q.den := by
    rw [← hnat]; exact dvd_pow_self 2 hNpos.ne'
  have : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
  norm_num at this

/-- **`log 2 / log 3` is irrational** — the reciprocal of an irrational nonzero real is
    irrational.  This is the independence hypothesis Baker's theorem needs for the bases `2, 3`. -/
theorem irrational_log_two_div_log_three : Irrational (Real.log 2 / Real.log 3) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hbase := irrational_log_three_div_log_two
  -- log 2 / log 3 = (log 3 / log 2)⁻¹
  have heq : Real.log 2 / Real.log 3 = (Real.log 3 / Real.log 2)⁻¹ := by
    rw [inv_div]
  rw [heq]
  exact hbase.inv

/-- **Flagship consequence of Baker's theorem (OQ-01).**  The linear form

        `log 2 + √2 · log 3`

    is transcendental.  Both summands are transcendental, but the new content — beyond
    Hermite–Lindemann and Gelfond–Schneider — is that they cannot cancel into an algebraic
    number, because `log 2` and `log 3` are `ℚ`-linearly independent and the coefficients
    `1, √2` are algebraic and not both zero.  This is the two-logarithm (`n = 2`) regime that
    single-logarithm transcendence theory does not reach. -/
theorem transcendental_log_two_add_sqrt_two_log_three :
    Transcendental ℚ (Real.log 2 + Real.sqrt 2 * Real.log 3) := by
  have h := baker_linear_form_two 2 3 (by norm_num) (by norm_num)
    two_algebraic three_algebraic irrational_log_two_div_log_three
    1 (Real.sqrt 2)
    one_algebraic sqrt_two_algebraic
    (by
      rintro ⟨h1, _⟩
      norm_num at h1)
  -- rewrite `1 * log 2 + √2 * log 3` to `log 2 + √2 * log 3`
  simpa [one_mul] using h

/-- **Collapsing sanity case.**  With both coefficients `1`, the two-logarithm form degenerates
    to a *single* logarithm `log 2 + log 3 = log 6`, and Baker's `n = 2` conclusion agrees with
    the single-logarithm Hermite–Lindemann fact that `log 6` is transcendental.  This contrasts
    with the flagship: an algebraic-irrational coefficient genuinely prevents the collapse. -/
theorem transcendental_log_six : Transcendental ℚ (Real.log 6) := by
  have h := baker_linear_form_two 2 3 (by norm_num) (by norm_num)
    two_algebraic three_algebraic irrational_log_two_div_log_three
    1 1
    one_algebraic one_algebraic
    (by rintro ⟨h1, _⟩; norm_num at h1)
  have hlog6 : Real.log 2 + Real.log 3 = Real.log 6 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  simpa [one_mul, hlog6] using h

#check @baker_linear_form_two
#check @sqrt_two_algebraic
#check @irrational_log_three_div_log_two
#check @irrational_log_two_div_log_three
#check @transcendental_log_two_add_sqrt_two_log_three
#check @transcendental_log_six

end GelfondSchneiderOQ01
