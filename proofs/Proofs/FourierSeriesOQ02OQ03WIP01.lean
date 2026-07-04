/-
# Sharpness of the Constant 1/2 in the Half-Period Fourier Decay Method

## Context (parent: `FourierSeriesOQ02OQ03` — sharp constant in Hölder Fourier decay)

`FourierSeriesOQ02.lean` proves the Hölder decay bound directly from the Fourier
integral, using the **half-period translation method**:

    2·ĉ_n(f) = ∫ (f(x) − f(x + T/(2n))) · e₋ₙ(x) dx      (difference formula)

Taking norms and using ‖e₋ₙ‖ = 1 with the probability measure `haarAddCircle` gives, for
any continuous `f` whose half-period difference is uniformly bounded by `M`,

    ‖ĉ_n(f)‖ ≤ M / 2.

Every appearance of the constant `1/2` in the decay theory (`decayConstant = 1/2` in the
parent `FourierSeriesOQ02OQ03`, the `C/2` of `fourierCoeff_holder_decay`) descends from this
single inequality. The parent file `FourierSeriesOQ02OQ03` *asserts* that `1/2` is optimal
but only studies formal properties of the bound expression; it never connects the constant to
an actual Fourier coefficient, nor exhibits a case of equality.

## What this file adds

We isolate the constant and prove it is **exactly the least possible constant in the
half-period method**, with a concrete case of equality:

* `fourierCoeff_le_half_uniformDiff` — the method bound `‖ĉ_n(f)‖ ≤ M/2` from a uniform
  half-period difference bound `M` (the abstraction underlying `fourierCoeff_holder_decay`:
  specializing `M = C·(T/(2|n|))^α` recovers the parent Hölder bound).
* `fourier_translate_halfperiod_pos` — translating a *positive* mode `fourier n` by its own
  half-period `T/(2n)` negates it.
* `fourier_halfperiod_diff_eq_two` — consequently the mode `fourier n` has half-period
  difference **exactly `2`** at every point: the difference saturates simultaneously for all
  `x`, which is precisely the mechanism the parent docstring names as the source of
  sharpness.
* `fourierCoeff_fourier_self` — orthonormality gives `ĉ_n(fourier n) = 1`.
* `halfPeriod_constant_sharp` — equality: `‖ĉ_n(fourier n)‖ = 2/2 = 1` while the uniform
  difference is `2`, so the method bound `M/2` is attained.
* `method_constant_ge_half` — **optimality**: any constant `k` for which `‖ĉ_n(f)‖ ≤ k·M`
  holds for all continuous `f` with uniform half-period difference `≤ M` must satisfy
  `1/2 ≤ k`. The witness is the pure mode.

**Self-containment.** The parent file `FourierSeriesOQ02` currently fails to build against
Mathlib 4.26.0 because a sibling optimality file (`FourierSeriesOQ02OQ04`, which it imports)
has unrelated `rpow`/tactic drift. To stay buildable this file imports only the pure-Mathlib
base `FourierSeriesOQ02Incomplete01` (for the measure-theoretic instances on `AddCircle T`
and `FourierDecayInfra.fourier_norm_eq_one`) and re-derives the small half-period
infrastructure it needs (`circleTranslate`, `halfPeriod`, the half-period negation identity,
and the difference formula). The proofs mirror those in `FourierSeriesOQ02`.

**Scope / honesty.** This establishes sharpness of the `1/2` *for the half-period method*:
no constant below `1/2` can replace it, and modes attain it. It does **not** settle the full
sharp-constant question for the Hölder class `k(α) = 1/2` — the Hölder bound has additional
slack `‖f(x)−f(x+h)‖ ≤ C·h^α` that pure modes (being smooth) do not saturate; the extremal
Hölder witnesses are the asymptotic piecewise-linear sawtooths noted in the parent, whose
exact coefficient computation remains open here.

Tags: fourier-analysis, holder-continuity, sharp-constant, extremal, add-circle
-/
import Proofs.FourierSeriesOQ02Incomplete01
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace FourierSharpMethod

open MeasureTheory Complex Topology Filter AddCircle FourierDecayInfra
open scoped Real

variable {T : ℝ} [hT : Fact (0 < T)]

/-
═══════════════════════════════════════════════════════════════════════════════
PART 0: HALF-PERIOD INFRASTRUCTURE (self-contained; mirrors FourierSeriesOQ02)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Translation of a point on `AddCircle T` by a real amount `s`. -/
def circleTranslate (s : ℝ) (x : AddCircle T) : AddCircle T :=
  x + ↑s

/-- The half-period for the `n`-th Fourier mode: `T/(2n)` (and `0` for `n = 0`). -/
def halfPeriod (T : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else T / (2 * ↑n)

/-- Translating the *conjugate* mode `fourier (-n)` by the half-period `T/(2n)` negates it. -/
theorem fourier_translate_halfperiod_neg (n : ℤ) (hn : n ≠ 0) (x : AddCircle T) :
    fourier (-n) (circleTranslate (halfPeriod T n) x) = -(fourier (-n) x) := by
  unfold circleTranslate halfPeriod
  simp only [hn, ite_false]
  rw [fourier_neg, fourier_neg]
  have h_eq : (T / (2 * (↑n : ℝ)) : ℝ) = T / 2 / ↑n := by ring
  rw [h_eq, fourier_add_half_inv_index hn hT.out]
  exact map_neg (starRingEnd ℂ) (fourier n x)

/-- **Difference formula** for Fourier coefficients:
    `2·ĉ_n(f) = ∫ (f(x) − f(x + T/(2n)))·e₋ₙ(x) dx`, from Haar translation invariance and
    the half-period sign flip. Mirrors `FourierSeriesOQ02.fourierCoeff_difference_formula`. -/
theorem fourierCoeff_difference_formula (f : AddCircle T → ℂ) (n : ℤ) (hn : n ≠ 0)
    (hf_cont : Continuous f) :
    2 * fourierCoeff f n =
      ∫ x : AddCircle T,
        (f x - f (circleTranslate (halfPeriod T n) x)) * fourier (-n) x ∂haarAddCircle := by
  unfold circleTranslate
  set s : AddCircle T := ↑(halfPeriod T n)
  have hp : ∀ x : AddCircle T, fourier (-n) (x + s) = -(fourier (-n) x) :=
    fun x => fourier_translate_halfperiod_neg n hn x
  have hpw : ∀ x : AddCircle T,
      (f x - f (x + s)) * fourier (-n) x =
      fourier (-n) x • f x + fourier (-n) (x + s) • f (x + s) := by
    intro x; simp only [smul_eq_mul, hp x]; ring
  simp_rw [hpw]
  have haar : ∫ x : AddCircle T, fourier (-n) (x + s) • f (x + s) ∂haarAddCircle =
      ∫ x, fourier (-n) x • f x ∂haarAddCircle :=
    integral_add_right_eq_self (μ := haarAddCircle) (fun x => fourier (-n) x • f x) s
  by_cases hint : Integrable (fun x => fourier (-n) x • f x) haarAddCircle
  · have h_split : ∫ x : AddCircle T,
        fourier (-n) x • f x + fourier (-n) (x + s) • f (x + s) ∂haarAddCircle =
        ∫ x, fourier (-n) x • f x ∂haarAddCircle +
        ∫ x, fourier (-n) (x + s) • f (x + s) ∂haarAddCircle :=
      integral_add hint ((measurePreserving_add_right haarAddCircle s).integrable_comp
        hint.aestronglyMeasurable |>.mpr hint)
    rw [h_split, haar]
    unfold fourierCoeff; ring
  · exfalso; apply hint
    rw [← integrableOn_univ]
    exact ((fourier (-n)).continuous.smul hf_cont).continuousOn.integrableOn_compact isCompact_univ

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE HALF-PERIOD METHOD BOUND (uniform difference ⟹ ‖ĉ_n‖ ≤ M/2)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Half-period method bound.** If the half-period difference of a continuous `f` is
    uniformly bounded by `M`, then `‖ĉ_n(f)‖ ≤ M/2`.

    This is the abstract inequality from which every `1/2` in the Hölder decay theory
    descends: taking `M = C·(T/(2|n|))^α` recovers the parent's `fourierCoeff_holder_decay`. -/
theorem fourierCoeff_le_half_uniformDiff (f : AddCircle T → ℂ) (hf : Continuous f)
    (n : ℤ) (hn : n ≠ 0) (M : ℝ)
    (hM : ∀ x, ‖f x - f (circleTranslate (halfPeriod T n) x)‖ ≤ M) :
    ‖fourierCoeff f n‖ ≤ M / 2 := by
  have hdiff := fourierCoeff_difference_formula f n hn hf
  have hbound : ‖2 * fourierCoeff f n‖ ≤ M := by
    rw [hdiff]
    calc ‖∫ x : AddCircle T,
            (f x - f (circleTranslate (halfPeriod T n) x)) * fourier (-n) x ∂haarAddCircle‖
        ≤ ∫ x : AddCircle T,
            ‖(f x - f (circleTranslate (halfPeriod T n) x)) * fourier (-n) x‖ ∂haarAddCircle :=
          norm_integral_le_integral_norm _
      _ = ∫ x : AddCircle T,
            ‖f x - f (circleTranslate (halfPeriod T n) x)‖ ∂haarAddCircle := by
          congr 1; ext x; rw [norm_mul, fourier_norm_eq_one, mul_one]
      _ ≤ ∫ _ : AddCircle T, M ∂haarAddCircle := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact Eventually.of_forall (fun x => norm_nonneg _)
          · exact integrable_const _
          · exact Eventually.of_forall hM
      _ = M := by rw [MeasureTheory.integral_const]; simp [smul_eq_mul]
  rw [norm_mul, norm_ofNat] at hbound
  linarith

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE PURE MODE SATURATES THE METHOD
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Translating the *positive* mode `fourier n` by its own half-period `T/(2n)` negates it. -/
theorem fourier_translate_halfperiod_pos (n : ℤ) (hn : n ≠ 0) (x : AddCircle T) :
    fourier n (circleTranslate (halfPeriod T n) x) = -(fourier n x) := by
  unfold circleTranslate halfPeriod
  simp only [hn, ite_false]
  have h_eq : (T / (2 * (↑n : ℝ))) = T / 2 / ↑n := by ring
  rw [h_eq, fourier_add_half_inv_index hn hT.out]

/-- **Uniform saturation.** The half-period difference of the mode `fourier n` equals `2`
    at *every* point `x`: the "difference saturates for every `x` simultaneously" mechanism
    the parent docstring identifies as the source of the sharp constant. -/
theorem fourier_halfperiod_diff_eq_two (n : ℤ) (hn : n ≠ 0) (x : AddCircle T) :
    ‖(fourier n : AddCircle T → ℂ) x
        - fourier n (circleTranslate (halfPeriod T n) x)‖ = 2 := by
  rw [fourier_translate_halfperiod_pos n hn x, sub_neg_eq_add]
  have h2 : (fourier n x : ℂ) + fourier n x = (2 : ℂ) * fourier n x := by ring
  rw [h2, norm_mul, fourier_norm_eq_one, mul_one, Complex.norm_ofNat]

/-- **Diagonal orthonormality.** `ĉ_n(fourier n) = 1`.
    `e₋ₙ · eₙ = e₀ ≡ 1`, and `∫ e₀ = 1` for the probability measure `haarAddCircle`. -/
theorem fourierCoeff_fourier_self (n : ℤ) :
    fourierCoeff (fourier n : AddCircle T → ℂ) n = 1 := by
  simp only [fourierCoeff, smul_eq_mul]
  have h_prod : ∀ x : AddCircle T, fourier (-n) x * fourier n x = (1 : ℂ) := by
    intro x
    rw [← fourier_add, neg_add_cancel, fourier_zero]
  simp_rw [h_prod]
  rw [MeasureTheory.integral_const]
  simp

/-- The coefficient norm of a pure mode is `1`. -/
theorem norm_fourierCoeff_fourier_self (n : ℤ) :
    ‖fourierCoeff (fourier n : AddCircle T → ℂ) n‖ = 1 := by
  rw [fourierCoeff_fourier_self, norm_one]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: SHARPNESS OF THE CONSTANT 1/2
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Equality in the method bound.** For the mode `fourier n` the uniform half-period
    difference is `M = 2`, and the coefficient norm equals `2/2 = 1`: the bound
    `‖ĉ_n(f)‖ ≤ M/2` of `fourierCoeff_le_half_uniformDiff` is *attained*. -/
theorem halfPeriod_constant_sharp (n : ℤ) (hn : n ≠ 0) :
    (∀ x, ‖(fourier n : AddCircle T → ℂ) x
        - fourier n (circleTranslate (halfPeriod T n) x)‖ = 2)
      ∧ ‖fourierCoeff (fourier n : AddCircle T → ℂ) n‖ = (2 : ℝ) / 2 := by
  refine ⟨fun x => fourier_halfperiod_diff_eq_two n hn x, ?_⟩
  rw [norm_fourierCoeff_fourier_self]; norm_num

/-- **Optimality of `1/2`.** Any constant `k` for which the half-period method bound
    `‖ĉ_n(f)‖ ≤ k·M` holds for *every* continuous `f` with uniform half-period difference
    `≤ M` must satisfy `1/2 ≤ k`. Hence `1/2` is the least admissible constant; the extremal
    witness is the pure mode `fourier n`. -/
theorem method_constant_ge_half (n : ℤ) (hn : n ≠ 0) (k : ℝ)
    (hk : ∀ (f : AddCircle T → ℂ), Continuous f → ∀ M : ℝ,
            (∀ x, ‖f x - f (circleTranslate (halfPeriod T n) x)‖ ≤ M) →
            ‖fourierCoeff f n‖ ≤ k * M) :
    1 / 2 ≤ k := by
  have hcont : Continuous (fourier n : AddCircle T → ℂ) := (fourier n).continuous
  have hM : ∀ x, ‖(fourier n : AddCircle T → ℂ) x
      - fourier n (circleTranslate (halfPeriod T n) x)‖ ≤ 2 :=
    fun x => le_of_eq (fourier_halfperiod_diff_eq_two n hn x)
  have h := hk (fourier n) hcont 2 hM
  rw [norm_fourierCoeff_fourier_self] at h
  -- h : 1 ≤ k * 2
  linarith

end FourierSharpMethod
