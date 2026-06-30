import Proofs.MeanValueTheoremOQ02OQ01
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Mean Value Theorem OQ-02-OQ-01-OQ-02: Taylor series of `sin` and `cos` converge on all of ℝ

## The open question (from `mean-value-theorem-oq-02-oq-01`)

The parent entry (`MeanValueTheoremOQ02OQ01`) distilled the Lagrange remainder into a
clean convergence engine:

* `taylorPolynomial_tendsto` — if a **single** constant `M` bounds *every* iterated
  derivative of `f` on an interval `(a,b)`, then the Taylor polynomials `Tₙ(b)` of `f`
  centered at `a` converge to `f(b)`.

It applied this to `exp`, but only for `x > 0`, because the derivative bound used there
(`exp x`) is interval-dependent and the engine requires the evaluation point to lie to
the *right* of the center.

The headline open question: **`sin` and `cos` converge on all of ℝ.** What makes them
qualitatively different from `exp` is that *all* of their iterated derivatives are
globally bounded by the single constant `M = 1` — independent of the point. This file:

* `abs_iteratedDeriv_sin_le_one`, `abs_iteratedDeriv_cos_le_one` — every iterated
  derivative of `sin`/`cos` is bounded in absolute value by `1` everywhere, read off
  Mathlib's even/odd derivative formulas.

* `taylorPolynomial_tendsto_globalBound` — upgrades the parent engine to a **two-sided**
  statement: a uniform global derivative bound forces `Tₙ(b) → f(b)` for **every** real
  `b` (left of the center, right of it, or at it). The negative side is handled by the
  reflection `t ↦ f(-t)`, whose Taylor polynomial at `-b` coincides with that of `f` at
  `b` (`reflect_taylor_eq`).

* `sin_taylor_tendsto`, `cos_taylor_tendsto` — the payoff: the Taylor series of `sin`
  and `cos` centered at `0` converge to `sin`/`cos` at **every** point of ℝ.

Nothing here re-derives a limit by hand: the convergence is funnelled entirely through
the parent's remainder estimate, with the global bound `M = 1` and the reflection trick
supplying the two ingredients the parent left open.
-/

open Real Set Filter Topology MeanValueTheoremOQ02 MeanValueTheoremOQ02OQ01

namespace MeanValueTheoremOQ02OQ01OQ02

/-!
## Part I: Global derivative bounds for `sin` and `cos`

Every iterated derivative of `sin` is one of `±sin`, `±cos`, hence bounded by `1`
everywhere. Mathlib records the even/odd derivative formulas, so the bound is immediate.
-/

/-- Every iterated derivative of `Real.sin` is bounded by `1` in absolute value, at
every point. This is the global, point-independent bound `M = 1`. -/
theorem abs_iteratedDeriv_sin_le_one (n : ℕ) (x : ℝ) :
    |iteratedDeriv n sin x| ≤ 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have e : iteratedDeriv (2 * m) sin x = (-1) ^ m * sin x := by
      rw [iteratedDeriv_even_sin]; simp [Pi.mul_apply]
    rw [e]
    calc |(-1 : ℝ) ^ m * sin x| = |sin x| := by
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      _ ≤ 1 := abs_le.mpr ⟨neg_one_le_sin x, sin_le_one x⟩
  · have e : iteratedDeriv (2 * m + 1) sin x = (-1) ^ m * cos x := by
      rw [iteratedDeriv_odd_sin]; simp [Pi.mul_apply]
    rw [e]
    calc |(-1 : ℝ) ^ m * cos x| = |cos x| := by
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      _ ≤ 1 := abs_le.mpr ⟨neg_one_le_cos x, cos_le_one x⟩

/-- Every iterated derivative of `Real.cos` is bounded by `1` in absolute value, at
every point. -/
theorem abs_iteratedDeriv_cos_le_one (n : ℕ) (x : ℝ) :
    |iteratedDeriv n cos x| ≤ 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have e : iteratedDeriv (2 * m) cos x = (-1) ^ m * cos x := by
      rw [iteratedDeriv_even_cos]; simp [Pi.mul_apply]
    rw [e]
    calc |(-1 : ℝ) ^ m * cos x| = |cos x| := by
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      _ ≤ 1 := abs_le.mpr ⟨neg_one_le_cos x, cos_le_one x⟩
  · have e : iteratedDeriv (2 * m + 1) cos x = (-1) ^ (m + 1) * sin x := by
      rw [iteratedDeriv_odd_cos]; simp [Pi.mul_apply]
    rw [e]
    calc |(-1 : ℝ) ^ (m + 1) * sin x| = |sin x| := by
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      _ ≤ 1 := abs_le.mpr ⟨neg_one_le_sin x, sin_le_one x⟩

/-!
## Part II: A two-sided convergence engine from a global bound

The parent's `taylorPolynomial_tendsto` requires the evaluation point `b` to lie to the
right of the center (`a < b`). With a *global* derivative bound we can also reach points
to the left, by reflecting through the origin: the function `g(t) = f(-t)` has the same
global bound, and its Taylor polynomial at `-b` equals that of `f` at `b`.
-/

/-- **Reflection identity for Taylor polynomials at `0`.** The `n`-th Taylor polynomial
of `t ↦ f(-t)` evaluated at `-b` equals the `n`-th Taylor polynomial of `f` at `b`.

The `(-1)ᵏ` from differentiating the reflection and the `(-1)ᵏ` from `(-b)ᵏ` cancel. -/
theorem reflect_taylor_eq (f : ℝ → ℝ) (n : ℕ) (b : ℝ) :
    taylorPolynomial (fun x => f (-x)) 0 n (-b) = taylorPolynomial f 0 n b := by
  simp only [taylorPolynomial, sub_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hD : iteratedDeriv k (fun x => f (-x)) 0 = (-1) ^ k * iteratedDeriv k f 0 := by
    have h := iteratedDeriv_comp_neg k f 0
    simpa using h
  have key : ((-1 : ℝ)) ^ k * (-b) ^ k = b ^ k := by
    rw [← mul_pow]; congr 1; ring
  rw [hD]
  linear_combination (iteratedDeriv k f 0 / (k.factorial : ℝ)) * key

/-- **Two-sided Taylor convergence from a uniform global derivative bound.**

If `f` is smooth and a single constant `M` bounds *every* iterated derivative of `f` at
*every* point of ℝ, then for **every** real `b` the Taylor polynomials of `f` centered at
`0` converge to `f(b)`.

Unlike the parent's one-sided `taylorPolynomial_tendsto`, this places no order constraint
between the center `0` and the evaluation point `b`: `b` may be positive, negative, or
zero. This is exactly the strength `sin` and `cos` enjoy (with `M = 1`). -/
theorem taylorPolynomial_tendsto_globalBound
    (f : ℝ → ℝ) (b M : ℝ)
    (hf : ContDiff ℝ ⊤ f)
    (hM : ∀ (n : ℕ) (x : ℝ), |iteratedDeriv n f x| ≤ M) :
    Tendsto (fun n => taylorPolynomial f 0 n b) atTop (𝓝 (f b)) := by
  rcases lt_trichotomy b 0 with hb | hb | hb
  · -- `b < 0`: reflect through the origin and apply the parent engine at `-b > 0`.
    have hb' : (0 : ℝ) < -b := by linarith
    have hg : ContDiff ℝ ⊤ (fun x => f (-x)) := hf.comp contDiff_neg
    have hgM : ∀ (n : ℕ), ∀ x ∈ Set.Ioo (0 : ℝ) (-b),
        |iteratedDeriv n (fun x => f (-x)) x| ≤ M := by
      intro n x _
      rw [iteratedDeriv_comp_neg, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one,
        one_pow, one_mul]
      exact hM n (-x)
    have key := taylorPolynomial_tendsto (fun x => f (-x)) 0 (-b) hb' M hg hgM
    have hval : (fun x => f (-x)) (-b) = f b := by simp
    rw [hval] at key
    exact key.congr (fun n => reflect_taylor_eq f n b)
  · -- `b = 0`: the Taylor polynomials are constantly `f 0`.
    subst hb
    have hconst : ∀ n, taylorPolynomial f 0 n 0 = f 0 := by
      intro n
      simp only [taylorPolynomial, sub_self]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k _ hk; simp [zero_pow hk]
      · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
    exact (tendsto_const_nhds (x := f 0)).congr (fun n => (hconst n).symm)
  · -- `0 < b`: the parent engine applies directly.
    exact taylorPolynomial_tendsto f 0 b hb M hf (fun n x _ => hM n x)

/-!
## Part III: Convergence of the Taylor series of `sin` and `cos` on all of ℝ

The global bound `M = 1` from Part I plugs straight into the two-sided engine of Part II.
-/

/-- **The Taylor series of `sin` converges to `sin` on all of ℝ.** For *every* real `x`
(positive, negative, or zero), the Taylor polynomials of `sin` centered at `0` converge
to `sin x`. -/
theorem sin_taylor_tendsto (x : ℝ) :
    Tendsto (fun n => taylorPolynomial sin 0 n x) atTop (𝓝 (sin x)) :=
  taylorPolynomial_tendsto_globalBound sin x 1 contDiff_sin
    (fun n y => abs_iteratedDeriv_sin_le_one n y)

/-- **The Taylor series of `cos` converges to `cos` on all of ℝ.** For *every* real `x`,
the Taylor polynomials of `cos` centered at `0` converge to `cos x`. -/
theorem cos_taylor_tendsto (x : ℝ) :
    Tendsto (fun n => taylorPolynomial cos 0 n x) atTop (𝓝 (cos x)) :=
  taylorPolynomial_tendsto_globalBound cos x 1 contDiff_cos
    (fun n y => abs_iteratedDeriv_cos_le_one n y)

end MeanValueTheoremOQ02OQ01OQ02
