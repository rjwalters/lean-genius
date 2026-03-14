/-
  Aristotle targets for Isoperimetric Inequality (area-of-circle-oq-01-oq-03)
  Routine supporting lemmas for automated proof search.
  See AreaOfCircleOQ01OQ03.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely provable from Mathlib
  - Clean theorem statement with no definition sorries
  - No axioms

  These two lemmas are the remaining gaps in the proof that
  fourier_decomposition is a theorem (was axiom). Both have
  clear proof outlines using existing Mathlib lemmas.
-/
import Mathlib

open Real Filter Topology Complex MeasureTheory

noncomputable section

namespace IsoperimetricOQAristotle

/-- Parseval identity for periodic real functions on [0, 2π].

    For a C¹ periodic function f : ℝ → ℝ, the integral of f² over [0, 2π]
    equals 2π times the sum of squared norms of its complex Fourier
    coefficients (computed via fourierCoeffOn on [0, 2π]).

    Proof strategy:
    1. Lift f to g : AddCircle(2π) → ℂ via AddCircle.liftIoc
    2. g is continuous (hence in L²) since f is C¹
    3. Apply tsum_sq_fourierCoeff to get Σ‖ĉₙ‖² = ∫_{AddCircle} ‖g‖² dμ
    4. Bridge: fourierCoeff_liftIoc_eq gives fourierCoeff g n = fourierCoeffOn hab f n
    5. Convert: ∫_{AddCircle} ‖g‖² dμ_Haar = (1/2π) ∫₀²π |f|²
       since haarAddCircle is the probability measure (total mass 1) -/
theorem parseval_periodic_real (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t) (hab : (0 : ℝ) < 2 * π)
    (ĉ : ℤ → ℂ) (hĉ : ĉ = fun n => fourierCoeffOn hab (ofReal ∘ f) n) :
    (Summable fun n => ‖ĉ n‖ ^ 2) ∧
    ∫ t in (0 : ℝ)..(2 * π), (f t : ℝ) ^ 2 =
      (2 * π) * ∑' n : ℤ, ‖ĉ n‖ ^ 2 := by
  sorry

/-- IBP for Fourier coefficients of periodic functions on [0, 2π].

    For a C¹ periodic function f with period 2π and n ≠ 0,
    the Fourier coefficient of the derivative equals in times
    the Fourier coefficient of f:
      ĉₙ(f') = in · ĉₙ(f)

    Proof strategy:
    1. Apply fourierCoeffOn_of_hasDerivAt (Mathlib) to get:
       ĉₙ(f) = 1/(-2πin) · (fourier(-n)(↑0) · (f(2π)-f(0)) - 2π · ĉₙ(f'))
    2. By periodicity: f(2π) = f(0), so f(2π) - f(0) = 0
    3. Simplify: ĉₙ(f) = 1/(-2πin) · (-2π · ĉₙ(f')) = ĉₙ(f') / (in)
    4. Rearrange: ĉₙ(f') = in · ĉₙ(f) -/
theorem fourierCoeffOn_deriv_periodic (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hab : (0 : ℝ) < 2 * π) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn hab (ofReal ∘ deriv f) n =
    I * ↑n * fourierCoeffOn hab (ofReal ∘ f) n := by
  -- Apply fourierCoeffOn_of_hasDerivAt (IBP for Fourier coefficients)
  have hle : (0 : ℝ) ≤ 2 * π := le_of_lt hab
  -- f composed with ofReal has derivative (ofReal ∘ deriv f) at each point
  have hderiv : ∀ x ∈ Set.uIcc 0 (2 * π),
      HasDerivAt (ofReal ∘ f) ((ofReal ∘ deriv f) x) x := by
    intro x _
    exact (hasDerivAt_ofReal_comp x (hf.differentiable le_rfl x).hasDerivAt)
  -- The derivative is interval-integrable (C¹ → continuous → integrable)
  have hint : IntervalIntegrable (ofReal ∘ deriv f) MeasureTheory.volume 0 (2 * π) := by
    apply Continuous.intervalIntegrable
    exact continuous_ofReal.comp (hf.continuous_deriv le_rfl)
  -- Apply the IBP formula
  have hibp := fourierCoeffOn_of_hasDerivAt hab n hderiv hint
  -- The boundary term vanishes: f(2π) - f(0) = 0 by periodicity
  have hperiod_eq : f (2 * π) = f 0 := by
    have := hperiod 0; simp at this; exact this
  -- Rearrange: from the IBP formula, extract ĉₙ(f') = in · ĉₙ(f)
  -- hibp says: fourierCoeffOn hab (ofReal ∘ f) n =
  --   1/(-2πin/(2π)) * (fourier(-n)(↑0) * (f(2π)-f(0)) - (2π) * fourierCoeffOn hab (ofReal ∘ deriv f) n)
  -- With f(2π) = f(0), the first term vanishes
  rw [hperiod_eq, sub_self, map_zero, zero_smul, zero_sub, neg_mul] at hibp
  -- Now hibp: fourierCoeffOn hab (ofReal ∘ f) n = (2π * fourierCoeffOn hab (ofReal ∘ deriv f) n) / (2πin/(2π))
  -- Solve for fourierCoeffOn hab (ofReal ∘ deriv f) n
  have hn' : (↑n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp at hibp ⊢
  linarith

end IsoperimetricOQAristotle
