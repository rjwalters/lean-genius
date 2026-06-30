/-
  Lebesgue Integral of Thomae's Function via the Bochner Integral

  Open Question (lebesgue-measure-oq-01-oq-02):
  Compute the Lebesgue integral of Thomae's (popcorn) function over `[0,1]`
  explicitly inside Mathlib's Bochner integral framework. The answer is `0`.

  The Thomae function
    f(x) = 1/q.den  if x = (q : ℝ) is rational (q in lowest terms)
    f(x) = 0        if x is irrational
  equals `0` almost everywhere, because `{x | f x ≠ 0} ⊆ range ((↑) : ℚ → ℝ)`
  is countable, and countable sets are `volume`-null (`ℝ` has no atoms).

  This file gives the genuine measure-theoretic (Bochner / lower-Lebesgue)
  computation. It is deliberately **self-contained**: `thomae` is defined and
  shown a.e.-zero here, with no dependence on sibling Thomae files (several of
  which target a different Mathlib snapshot). Everything below type-checks
  against the pinned `Mathlib v4.26.0`. We record:

    * the global Bochner integral over all of `ℝ`            (`∫ x, thomae x ∂volume`),
    * the Bochner *set* integrals over `Icc 0 1` and `Ioc 0 1`
      (`∫ x in s, thomae x ∂volume`, i.e. integration against `volume.restrict s`),
    * the lower-Lebesgue integral of the nonnegative integrand
      (`∫⁻ x, ENNReal.ofReal (thomae x) ∂volume`), globally and on `Icc 0 1`,
    * and the agreement of the Bochner integral with `(∫⁻ …).toReal`.

  No sorries, no axioms.
-/
import Mathlib

open MeasureTheory Set

namespace LebesgueMeasureOQ01OQ02

/-!
## The Thomae function and its a.e.-vanishing
-/

open Classical in
/-- Thomae's function (popcorn function): `1/q.den` if `x` is rational
    (`q` canonical, `q.den` its denominator in lowest terms), `0` if irrational. -/
noncomputable def thomae : ℝ → ℝ := fun x =>
  if h : ∃ q : ℚ, (q : ℝ) = x then 1 / (h.choose.den : ℝ) else 0

/-- Off the rationals, Thomae's function vanishes. -/
theorem thomae_irrational {x : ℝ} (hx : Irrational x) : thomae x = 0 := by
  unfold thomae
  rw [dif_neg]
  rintro ⟨q, hq⟩
  exact hx ⟨q, hq⟩

/-- Thomae's function is nonnegative. -/
theorem thomae_nonneg (x : ℝ) : 0 ≤ thomae x := by
  unfold thomae; split_ifs <;> positivity

/-- The support of Thomae's function lies in the image of `ℚ` in `ℝ`:
    `thomae x ≠ 0` forces `x` to be rational. (`Irrational x` is by definition
    `x ∉ Set.range ((↑) : ℚ → ℝ)`.) -/
theorem thomae_support_subset_rat :
    {x : ℝ | thomae x ≠ 0} ⊆ Set.range ((↑) : ℚ → ℝ) := by
  intro x hx
  by_contra h
  exact hx (thomae_irrational h)

/-- The support of Thomae's function is null: it lies in the countable set
    `range ((↑) : ℚ → ℝ)`, which has `volume`-measure zero (`ℝ` has `NoAtoms`). -/
theorem thomae_support_null : volume {x : ℝ | thomae x ≠ 0} = 0 :=
  measure_mono_null thomae_support_subset_rat
    ((Set.countable_range ((↑) : ℚ → ℝ)).measure_zero volume)

/-- Thomae's function is `volume`-a.e. equal to the zero function. -/
theorem thomae_ae_eq_zero : thomae =ᵐ[volume] 0 := by
  refine (ae_iff).mpr ?_
  simp only [Pi.zero_apply]
  exact thomae_support_null

/-- Thomae's function is integrable (it agrees a.e. with the zero function). -/
theorem thomae_integrable : Integrable thomae volume :=
  (integrable_zero ℝ ℝ volume).congr thomae_ae_eq_zero.symm

/-!
## Global Bochner integral over `ℝ`
-/

/-- The Bochner integral of Thomae's function over all of `ℝ` is `0`
    (the function is `volume`-a.e. equal to `0`). -/
theorem thomae_integral_univ_zero : ∫ x, thomae x ∂volume = 0 := by
  rw [integral_congr_ae thomae_ae_eq_zero]; simp

/-!
## Bochner set integrals over `[0,1]`
-/

/-- The Bochner set integral of Thomae's function over `Icc 0 1` is `0`.
    `∫ x in s, f x ∂μ` is integration against `μ.restrict s`; a.e.-vanishing
    is inherited by the restricted measure (`ae_restrict_of_ae`). -/
theorem thomae_setIntegral_Icc_zero :
    ∫ x in Set.Icc (0:ℝ) 1, thomae x ∂volume = 0 := by
  rw [integral_congr_ae (ae_restrict_of_ae thomae_ae_eq_zero)]; simp

/-- The Bochner set integral over the half-open interval `Ioc 0 1` is `0`.
    This is exactly the set integral that `∫ x in (0:ℝ)..1, thomae x` unfolds to
    (via `intervalIntegral.integral_of_le`), so it is the genuine Bochner form of
    the classical "popcorn integral". -/
theorem thomae_setIntegral_Ioc_zero :
    ∫ x in Set.Ioc (0:ℝ) 1, thomae x ∂volume = 0 := by
  rw [integral_congr_ae (ae_restrict_of_ae thomae_ae_eq_zero)]; simp

/-- The interval ("Riemann-style") integral over `[0,1]`, recovered from the
    Bochner machinery. -/
theorem thomae_intervalIntegral_zero :
    ∫ x in (0:ℝ)..1, thomae x = 0 := by
  have h : (∫ x in (0:ℝ)..1, thomae x) = ∫ _ in (0:ℝ)..1, (0:ℝ) :=
    intervalIntegral.integral_congr_ae (thomae_ae_eq_zero.mono (fun x hx _ => hx))
  rw [h, intervalIntegral.integral_zero]

/-!
## Lower-Lebesgue integral of the nonnegative integrand
-/

/-- The `ENNReal`-valued nonnegative integrand `ENNReal.ofReal ∘ thomae` is
    `volume`-a.e. equal to `0`. -/
theorem thomae_ofReal_ae_eq_zero :
    (fun x => ENNReal.ofReal (thomae x)) =ᵐ[volume] 0 := by
  filter_upwards [thomae_ae_eq_zero] with x hx
  simp only [Pi.zero_apply] at hx ⊢
  rw [hx, ENNReal.ofReal_zero]

/-- The lower-Lebesgue integral (`∫⁻`) of the nonnegative integrand over all of
    `ℝ` is `0`. This is the textbook "Lebesgue integral of a nonnegative
    function" and matches the Bochner integral for the integrable `thomae`. -/
theorem thomae_lintegral_univ_zero :
    ∫⁻ x, ENNReal.ofReal (thomae x) ∂volume = 0 := by
  rw [lintegral_congr_ae thomae_ofReal_ae_eq_zero]; simp

/-- The lower-Lebesgue integral of the nonnegative integrand over `Icc 0 1`
    is `0`. -/
theorem thomae_lintegral_Icc_zero :
    ∫⁻ x in Set.Icc (0:ℝ) 1, ENNReal.ofReal (thomae x) ∂volume = 0 := by
  rw [lintegral_congr_ae (ae_restrict_of_ae thomae_ofReal_ae_eq_zero)]; simp

/-!
## Agreement of the Bochner and lower-Lebesgue integrals
-/

/-- For the nonnegative, integrable `thomae`, the Bochner integral over `[0,1]`
    agrees with `(∫⁻ …).toReal` — both are `0`. This makes explicit that the
    "Lebesgue integral" computed via the Bochner framework coincides with the
    classical lower-Lebesgue integral of a nonnegative function. -/
theorem thomae_bochner_eq_lintegral_toReal :
    ∫ x in Set.Icc (0:ℝ) 1, thomae x ∂volume
      = (∫⁻ x in Set.Icc (0:ℝ) 1, ENNReal.ofReal (thomae x) ∂volume).toReal := by
  rw [thomae_setIntegral_Icc_zero, thomae_lintegral_Icc_zero, ENNReal.toReal_zero]

end LebesgueMeasureOQ01OQ02
