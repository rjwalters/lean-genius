import Mathlib

/-
# The Mellin transform of the unit indicator and its convergence strip

The Mellin transform of a function `f : (0, ∞) → ℂ` is
`mellin f s = ∫_{0}^{∞} t^{s-1} f(t) dt`.
The simplest non-trivial example is the indicator of the half-open unit
interval `(0, 1]`, whose Mellin transform is the meromorphic kernel `1/s`:
`∫_{0}^{1} t^{s-1} dt = 1/s` whenever `Re s > 0`.

Mathlib proves the *forward* statement `hasMellin_one_Ioc`: for `Re s > 0` the
transform exists and equals `1/s`. This entry packages that base case and then
adds two genuinely new results that Mathlib does not state:

* **Sharp convergence strip** (`mellinConvergent_unitIndicator_iff`): the Mellin
  integral of `𝟙_{(0,1]}` converges *if and only if* `Re s > 0`. Mathlib only
  records the `←` direction (via `hasMellin_one_Ioc`); the boundary `Re s = 0`
  is where `∫_0^1 t^{-1} dt` diverges, so the open half-plane `Re s > 0` is
  *exactly* the region of absolute convergence. The reverse implication is
  obtained from `integrableOn_Ioo_cpow_iff`, which characterises the
  integrability of `t ↦ t^{σ}` near `0`.

* **Scaling law** (`hasMellin_indicator_Ioc`): for any cut-off `a > 0`,
  `mellin 𝟙_{(0,a]} s = a^{s} / s`. This follows from the dilation rule
  `mellin_comp_mul_left` applied to the base case. Specialising to `s = 1`
  recovers the Lebesgue measure of the interval: `mellin 𝟙_{(0,a]} 1 = a`.

Everything is built on Mathlib's `MellinTransform` and rpow-integrability API,
so the headline reuses Mathlib results (badge `mathlib`), but the convergence
*iff* and the scaling law are not stated there.
-/

open Complex MeasureTheory Set

namespace MellinPowerConvergenceOQ01

/-- The unit indicator `𝟙_{(0,1]}` valued in `ℂ`. -/
noncomputable abbrev unitIndicator : ℝ → ℂ := Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => 1)

/-! ## Base case: the Mellin transform of `𝟙_{(0,1]}` is `1/s` -/

/-- **Base case (re-export).** For `Re s > 0` the Mellin transform of the unit
indicator exists and equals `1/s`. This is Mathlib's `hasMellin_one_Ioc`. -/
theorem hasMellin_unitIndicator {s : ℂ} (hs : 0 < s.re) :
    HasMellin unitIndicator s (1 / s) :=
  hasMellin_one_Ioc hs

/-- The value of the transform: `mellin 𝟙_{(0,1]} s = 1/s` for `Re s > 0`. -/
theorem mellin_unitIndicator {s : ℂ} (hs : 0 < s.re) :
    mellin unitIndicator s = 1 / s :=
  (hasMellin_one_Ioc hs).2

/-! ## Sharp convergence strip: convergence ⇔ `Re s > 0` -/

/-- **Sharp convergence strip.** The Mellin integral of the unit indicator
converges if and only if `Re s > 0`. Mathlib only proves the `←` direction; the
`→` direction pins the boundary `Re s = 0`, where `∫_0^1 t^{-1} dt` diverges. -/
theorem mellinConvergent_unitIndicator_iff {s : ℂ} :
    MellinConvergent unitIndicator s ↔ 0 < s.re := by
  have aux : MeasurableSet (Set.Ioc (0 : ℝ) 1) := measurableSet_Ioc
  -- The Mellin integrand is the indicator of `(0,1]` applied to the pure power `t^{s-1}`.
  have hfun : (fun t : ℝ => (t : ℂ) ^ (s - 1) • unitIndicator t)
      = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun t : ℝ => (t : ℂ) ^ (s - 1)) := by
    funext t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · simp only [unitIndicator, Set.indicator_of_mem ht, smul_eq_mul, mul_one]
    · simp only [unitIndicator, Set.indicator_of_notMem ht, smul_zero]
  rw [MellinConvergent, hfun, IntegrableOn, integrable_indicator_iff aux, IntegrableOn,
    Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self, ← IntegrableOn,
    integrableOn_Ioc_iff_integrableOn_Ioo, intervalIntegral.integrableOn_Ioo_cpow_iff (zero_lt_one),
    Complex.sub_re, Complex.one_re]
  constructor <;> intro h <;> linarith

/-! ## Scaling law: `mellin 𝟙_{(0,a]} s = a^s / s` -/

/-- **Scaling law.** For any `a > 0` and `Re s > 0`, the Mellin transform of the
indicator of `(0, a]` exists and equals `a^s / s`. Specialising to `a = 1`
recovers the base case. -/
theorem hasMellin_indicator_Ioc {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (Set.indicator (Set.Ioc (0 : ℝ) a) (fun _ => 1)) s ((a : ℂ) ^ s / s) := by
  have hinv : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha
  -- Membership transfer under the dilation `t ↦ a⁻¹ * t`.
  have hmem : ∀ t : ℝ, (a⁻¹ * t ∈ Set.Ioc (0 : ℝ) 1) ↔ (t ∈ Set.Ioc (0 : ℝ) a) := by
    intro t
    simp only [Set.mem_Ioc]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨(mul_pos_iff_of_pos_left hinv).mp h0, by rwa [inv_mul_le_iff₀ ha, mul_one] at h1⟩
    · rintro ⟨h0, h1⟩
      exact ⟨mul_pos hinv h0, by rw [inv_mul_le_iff₀ ha, mul_one]; exact h1⟩
  -- `𝟙_{(0,a]}(t) = 𝟙_{(0,1]}(a⁻¹ t)`.
  have hfun : Set.indicator (Set.Ioc (0 : ℝ) a) (fun _ => (1 : ℂ))
      = fun t => Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℂ)) (a⁻¹ * t) := by
    funext t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) a
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ((hmem t).mpr ht)]
    · rw [Set.indicator_of_notMem ht,
        Set.indicator_of_notMem (fun h => ht ((hmem t).mp h))]
  refine ⟨?_, ?_⟩
  · -- convergence via the dilation rule
    rw [hfun]
    exact (MellinConvergent.comp_mul_left hinv).mpr (hasMellin_one_Ioc hs).1
  · -- value via the dilation rule
    rw [hfun, mellin_comp_mul_left _ s hinv, (hasMellin_one_Ioc hs).2,
      Complex.ofReal_inv, Complex.cpow_neg,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg ha.le]; exact Real.pi_pos.ne),
      inv_inv, smul_eq_mul, mul_one_div]

/-- The value form of the scaling law. -/
theorem mellin_indicator_Ioc {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    mellin (Set.indicator (Set.Ioc (0 : ℝ) a) (fun _ => 1)) s = (a : ℂ) ^ s / s :=
  (hasMellin_indicator_Ioc ha hs).2

/-! ## Measure interpretation at `s = 1` -/

/-- At `s = 1` the Mellin transform of `𝟙_{(0,a]}` returns the length of the
interval: `mellin 𝟙_{(0,a]} 1 = a`. -/
theorem mellin_indicator_Ioc_one {a : ℝ} (ha : 0 < a) :
    mellin (Set.indicator (Set.Ioc (0 : ℝ) a) (fun _ => 1)) 1 = (a : ℂ) := by
  rw [mellin_indicator_Ioc ha (by norm_num), Complex.cpow_one, div_one]

/-- The unit interval has length `1`: `mellin 𝟙_{(0,1]} 1 = 1`. -/
theorem mellin_unitIndicator_one :
    mellin unitIndicator 1 = 1 := by
  have := mellin_indicator_Ioc_one (a := 1) one_pos
  simpa using this

end MellinPowerConvergenceOQ01
