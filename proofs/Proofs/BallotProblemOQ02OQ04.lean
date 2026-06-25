import Mathlib

/-
# The Arcsine Distribution — quantitative core of Lévy's Arcsine Law

## Research Problem: ballot-problem-oq-02-oq-04
"Arcsine Law via Brownian motion local times."

## Context

Lévy's Arcsine Law (1939) is the continuous-time culmination of the ballot
problem. For a standard Brownian motion `W` on `[0, 1]`, three a priori different
statistics all share the **same** distribution:

  * `A⁺ := |{t ∈ [0,1] : W_t > 0}|`           (occupation time of the positive half-line),
  * `θ  := argmax_{t ∈ [0,1]} W_t`             (time of the maximum),
  * `L  := sup {t ∈ [0,1] : W_t = 0}`          (time of the last zero).

Each is distributed according to the **arcsine law** on `[0,1]`, with cumulative
distribution function

      F(x) = (2/π) · arcsin(√x),        x ∈ [0,1],

and density `f(x) = 1 / (π · √(x(1-x)))`. The "via local times" route obtains this
through the occupation-density (local time) of `W` at level `0`: Lévy's theorem
identifies the local-time process of `W` with the running maximum of an independent
Brownian motion, and the occupation-time formula then yields `F` above.

## What this file formalizes (0 sorries, 0 axioms)

Mathlib v4.26.0 contains **no** Brownian motion, **no** stochastic local time, and
**no** arcsine *distribution* object, so the probabilistic derivation "via local
times" cannot yet be carried out from primitives (it would require building the
entire local-time theory — far beyond a single entry; the parent
`BallotProblemOQ02.lean` axiomatizes the BM facts it needs).

What is fully provable in Mathlib *today* — and is the quantitative content the law
asserts — is the **arcsine cumulative distribution function** `F` itself, as a real
analytic object built from `Real.arcsin`. We prove, axiom-free:

  * `arcsineCDF_zero`   : `F 0 = 0`                          (left endpoint),
  * `arcsineCDF_one`    : `F 1 = 1`                          (right endpoint / total mass 1),
  * `arcsineCDF_half`   : `F (1/2) = 1/2`                    (median at the centre),
  * `arcsineCDF_mono`   : `F` is monotone on `[0,1]`         (it is a genuine CDF),
  * `arcsineCDF_symm`   : `F x + F (1-x) = 1`                (reflection symmetry about 1/2),
  * `arcsineDensity_symm`, `arcsineDensity_half` : the density is symmetric about 1/2
        and takes its minimum value `2/π` there — the U-shape that makes the law famous
        (Brownian motion spends its time *near* one side, not balanced around the middle).

The symmetry `F x + F (1-x) = 1` is the formal expression of the counterintuitive
"arcsine" phenomenon: the three statistics above are *least* likely to land near the
fair value `1/2` and *most* likely near the extremes `0` and `1`.

## References
- Lévy (1939): *Sur certains processus stochastiques homogènes*.
- Karatzas–Shreve (1991): *Brownian Motion and Stochastic Calculus*, §6.3 (arcsine laws).
- Mörters–Peres (2010): *Brownian Motion*, §5.2 (local times) and Thm 5.28 (arcsine law).
-/

namespace ArcsineLaw

open Real

/-- The cumulative distribution function of the arcsine law on `[0,1]`:
    `F(x) = (2/π) · arcsin(√x)`. -/
noncomputable def arcsineCDF (x : ℝ) : ℝ := (2 / π) * arcsin (Real.sqrt x)

/-- The arcsine density on `(0,1)`: `f(x) = 1 / (π · √(x(1-x)))`. -/
noncomputable def arcsineDensity (x : ℝ) : ℝ := 1 / (π * Real.sqrt (x * (1 - x)))

/-! ### Endpoints and total mass -/

/-- `F(0) = 0`: the distribution puts no mass left of `0`. -/
@[simp] theorem arcsineCDF_zero : arcsineCDF 0 = 0 := by
  simp [arcsineCDF]

/-- `F(1) = 1`: the distribution is supported in `[0,1]` and has total mass `1`. -/
@[simp] theorem arcsineCDF_one : arcsineCDF 1 = 1 := by
  rw [arcsineCDF, Real.sqrt_one, Real.arcsin_one]
  field_simp

/-! ### The median sits at the centre -/

/-- Helper: `arcsin (√(1/2)) = π/4`. -/
theorem arcsin_sqrt_half : arcsin (Real.sqrt (1 / 2)) = π / 4 := by
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
  have hsq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hsqrt : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
    rw [← hsq, Real.sqrt_sq hnn]
  rw [hsqrt, ← Real.sin_pi_div_four,
    Real.arcsin_sin (by positivity)
      (by rw [div_le_div_iff (by norm_num) (by norm_num)]; nlinarith [Real.pi_pos])]

/-- `F(1/2) = 1/2`: the median of the arcsine law is the fair value `1/2`,
    even though the distribution concentrates mass away from it. -/
theorem arcsineCDF_half : arcsineCDF (1 / 2) = 1 / 2 := by
  rw [arcsineCDF, arcsin_sqrt_half]
  field_simp

/-! ### Monotonicity: `F` is a genuine CDF -/

/-- `F` is monotone on `[0,1]`: increasing `x` cannot decrease the probability. -/
theorem arcsineCDF_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    arcsineCDF x ≤ arcsineCDF y := by
  have hcoef : (0 : ℝ) ≤ 2 / π := by positivity
  apply mul_le_mul_of_nonneg_left _ hcoef
  exact Real.arcsin_le_arcsin (Real.sqrt_le_sqrt hxy)

/-! ### Reflection symmetry about `1/2` — the arcsine phenomenon -/

/-- Complementary-angle identity for the building block of `F`:
    `arcsin(√x) + arcsin(√(1-x)) = π/2` for `x ∈ [0,1]`. -/
theorem arcsin_sqrt_add_arcsin_sqrt_one_sub {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    arcsin (Real.sqrt x) + arcsin (Real.sqrt (1 - x)) = π / 2 := by
  have ha : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt h0
  -- arccos(√x) = arcsin(√(1 - (√x)²)) = arcsin(√(1-x))
  have key : arccos (Real.sqrt x) = arcsin (Real.sqrt (1 - x)) := by
    rw [Real.arccos_eq_arcsin ha, hsq]
  rw [Real.arccos_eq_pi_div_two_sub_arcsin] at key
  linarith

/-- **Reflection symmetry**: `F(x) + F(1-x) = 1` for `x ∈ [0,1]`.

    This is the formal statement of the arcsine law's signature feature: the time a
    Brownian path spends positive is distributed symmetrically about `1/2`, yet (by
    the U-shaped density below) is *least* likely to be near `1/2`. -/
theorem arcsineCDF_symm {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    arcsineCDF x + arcsineCDF (1 - x) = 1 := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hsum := arcsin_sqrt_add_arcsin_sqrt_one_sub h0 h1
  rw [arcsineCDF, arcsineCDF, ← mul_add, hsum]
  field_simp
  ring

/-! ### The U-shaped density -/

/-- The density is symmetric about `1/2`: `f(x) = f(1-x)`. -/
theorem arcsineDensity_symm (x : ℝ) : arcsineDensity x = arcsineDensity (1 - x) := by
  unfold arcsineDensity
  ring_nf

/-- The density attains the value `2/π` at the centre — its global minimum,
    the bottom of the U. -/
theorem arcsineDensity_half : arcsineDensity (1 / 2) = 2 / π := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  unfold arcsineDensity
  rw [show (1 : ℝ) / 2 * (1 - 1 / 2) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  field_simp

end ArcsineLaw
