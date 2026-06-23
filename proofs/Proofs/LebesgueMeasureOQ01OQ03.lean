import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-
# Indicator Integral Zero for Null Sets (OQ-01-OQ-03)

## The Question

Can the result from `LebesgueMeasureOQ01` (that the Dirichlet function 𝟙_ℚ
has Lebesgue integral zero) be extended to show that the indicator of ANY
set with Lebesgue measure zero has integral zero?

## Answer: Yes. We prove the fully general result.

**Main Theorem**: For any set S with μ(S) = 0,
  ∫ 𝟙_S dμ = 0.

This subsumes the Dirichlet function result (OQ-01) as the special case S = ℚ.

## Proof Strategy

The proof has three steps:

1. **Null set → a.e. complement**: μ(S) = 0 implies that almost every x lies
   outside S. Formally: sᶜ ∈ μ.ae, which is `compl_mem_ae_iff.mpr hs`.

2. **Off S → indicator is zero**: If x ∉ S, then by definition of the
   indicator function, 𝟙_S(x) = 0. This is `Set.indicator_of_notMem`.

3. **A.e. zero → integral zero**: Since 𝟙_S = 0 a.e., the integral is zero.
   This is `integral_eq_zero_of_ae`.

The same chain gives ∫_T 𝟙_S dμ = 0 for any T (using `ae_restrict_of_ae`).

## Mathematical Context

Lebesgue integration is "blind" to null sets: changing a function on a
measure-zero set leaves the integral unchanged. The indicator 𝟙_S of a
null set S is exactly 0 almost everywhere, so its integral is 0.

This principle extends to arbitrary integrands on null sets: ∫_S f dμ = 0
for any f (regardless of integrability) when μ(S) = 0. In Lean's Bochner
integral, the integral over the zero measure is 0 by convention, and
μ.restrict S = 0 whenever μ(S) = 0.

## Examples of null sets in ℝ
- ℚ (countable → measure zero): the Dirichlet function case
- Any countable set {x₁, x₂, ...}
- Any single point {a}
- Countable unions of null sets
- The Cantor set (closed, uncountable, measure zero)
-/

open MeasureTheory Measure Set Filter

namespace LebesgueMeasureOQ01OQ03

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: CORE ABSTRACT THEOREMS (ANY MEASURE SPACE)
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **Core Lemma**: If μ(S) = 0, then the indicator 𝟙_S is zero
    almost everywhere.
    Works in any measure space. -/
theorem indicator_ae_zero_of_null {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : Set α) (hs : μ s = 0) :
    ∀ᵐ x ∂μ, s.indicator (fun _ => (1 : ℝ)) x = 0 := by
  filter_upwards [compl_mem_ae_iff.mpr hs] with x hx
  exact Set.indicator_of_notMem hx _

/-- **Main Theorem**: For any set S with μ(S) = 0, the Bochner integral
    of the indicator function 𝟙_S is zero:

    ∫ 𝟙_S dμ = 0.

    This holds in any measure space without requiring S to be measurable.
    (Measurability of S would be needed for the converse direction.) -/
theorem integral_indicator_of_null {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : Set α) (hs : μ s = 0) :
    ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ = 0 := by
  apply integral_eq_zero_of_ae
  exact indicator_ae_zero_of_null s hs

/-- **Restricted form**: ∫_T 𝟙_S dμ = 0 for any region T, when μ(S) = 0.
    The indicator is still a.e. zero even when restricted to T. -/
theorem integral_indicator_of_null_on_set {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (s t : Set α) (hs : μ s = 0) :
    ∫ x in t, s.indicator (fun _ => (1 : ℝ)) x ∂μ = 0 := by
  apply integral_eq_zero_of_ae
  apply ae_restrict_of_ae
  exact indicator_ae_zero_of_null s hs

/-- **Product integrand**: ∫ f·𝟙_S dμ = 0 for any f, any T, when μ(S) = 0.
    Multiplying by f doesn't matter: 𝟙_S = 0 a.e. forces the product
    to zero a.e. -/
theorem integral_mul_indicator_of_null {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (s t : Set α) (hs : μ s = 0) :
    ∫ x in t, f x * s.indicator (fun _ => (1 : ℝ)) x ∂μ = 0 := by
  apply integral_eq_zero_of_ae
  apply ae_restrict_of_ae
  filter_upwards [compl_mem_ae_iff.mpr hs] with x hx
  simp [Set.indicator_of_notMem hx]

/-- **Integrating over a null set is zero**: ∫_S f dμ = 0 for any f,
    when μ(S) = 0. This holds because μ.restrict S = 0, and the Bochner
    integral over the zero measure is zero by convention. -/
theorem integral_on_null_set {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (s : Set α) (hs : μ s = 0) :
    ∫ x in s, f x ∂μ = 0 := by
  have h : μ.restrict s = 0 := Measure.restrict_zero_set hs
  rw [h]
  exact integral_zero_measure f

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: LEBESGUE MEASURE ON ℝ
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **Borel null set in ℝ**: For any set B ⊆ ℝ with Lebesgue measure
    zero, ∫ 𝟙_B dλ = 0. -/
theorem integral_indicator_borel_null (B : Set ℝ) (hB : volume B = 0) :
    ∫ x, B.indicator (fun _ => (1 : ℝ)) x ∂volume = 0 :=
  integral_indicator_of_null B hB

/-- **Countable sets**: Any countable subset of ℝ has Lebesgue measure
    zero, hence zero indicator integral. -/
theorem integral_indicator_countable (s : Set ℝ) (hs : s.Countable) :
    ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂volume = 0 :=
  integral_indicator_of_null s (hs.measure_zero volume)

/-- **Finite sets** have measure zero in ℝ. -/
theorem integral_indicator_finite (s : Set ℝ) (hs : s.Finite) :
    ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂volume = 0 :=
  integral_indicator_countable s hs.countable

/-- **Single points**: ∫ 𝟙_{a} dλ = 0 for any a ∈ ℝ. -/
theorem integral_indicator_singleton (a : ℝ) :
    ∫ x, ({a} : Set ℝ).indicator (fun _ => (1 : ℝ)) x ∂volume = 0 :=
  integral_indicator_finite {a} (Set.finite_singleton a)

/-- **The Dirichlet function**: ∫ 𝟙_ℚ dλ = 0. This is the OQ-01 result,
    now a special case of the general theorem. -/
theorem integral_indicator_rationals :
    ∫ x, Set.indicator (Set.range (Rat.cast : ℚ → ℝ)) (fun _ => (1 : ℝ)) x ∂volume = 0 :=
  integral_indicator_countable _ (Set.countable_range _)

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: COUNTABLE UNIONS OF NULL SETS
═══════════════════════════════════════════════════════════════════════════════
-/

/-- A countable union of measurable null sets is a null set. -/
theorem measure_iUnion_null_of_null {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (s : ℕ → Set α)
    (hs_null : ∀ n, μ (s n) = 0) :
    μ (⋃ n, s n) = 0 :=
  measure_iUnion_null fun n => hs_null n

/-- The indicator of a countable union of null sets has zero integral. -/
theorem integral_indicator_iUnion_null (s : ℕ → Set ℝ)
    (hs_null : ∀ n, volume (s n) = 0) :
    ∫ x, (⋃ n, s n).indicator (fun _ => (1 : ℝ)) x ∂volume = 0 :=
  integral_indicator_of_null _ (measure_iUnion_null_of_null s hs_null)

/-- Integration over a countable union of null sets is zero. -/
theorem integral_on_iUnion_null_set {f : ℝ → ℝ} (s : ℕ → Set ℝ)
    (hs_null : ∀ n, volume (s n) = 0) :
    ∫ x in ⋃ n, s n, f x ∂volume = 0 :=
  integral_on_null_set _ (measure_iUnion_null_of_null s hs_null)

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: A.E. INVARIANCE OF THE INTEGRAL
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **A.e. equality preserves the integral**: Two functions that agree
    outside a null set have the same integral. This is the general principle:
    Lebesgue integration is invariant under modifications on null sets. -/
theorem integral_congr_ae_null_change {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} {s : Set α}
    (hs : μ s = 0) (h_off_s : ∀ x ∉ s, f x = g x) :
    ∫ x, f x ∂μ = ∫ x, g x ∂μ := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [compl_mem_ae_iff.mpr hs] with x hx
  exact h_off_s x hx

/-- **A.e. zero → integral zero**: Direct corollary of the above. -/
theorem integral_eq_zero_of_ae_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (h : ∀ᵐ x ∂μ, f x = 0) :
    ∫ x, f x ∂μ = 0 :=
  integral_eq_zero_of_ae h

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: SUBSUMES OQ-01 RESULTS
═══════════════════════════════════════════════════════════════════════════════
-/

/-- The OQ-01 result (Dirichlet function has zero integral) is the special
    case of the general theorem with S = ℚ.
    This is a direct import of the OQ-01 conclusion from the general theorem. -/
example : ∫ x in Set.Icc (0:ℝ) 1,
    Set.indicator (Set.range (Rat.cast : ℚ → ℝ)) (fun _ => (1 : ℝ)) x ∂volume = 0 :=
  integral_indicator_of_null_on_set _ _ (Set.countable_range (Rat.cast : ℚ → ℝ) |>.measure_zero volume)

/-
═══════════════════════════════════════════════════════════════════════════════
SUMMARY
═══════════════════════════════════════════════════════════════════════════════

## Answer to OQ-01-OQ-03

YES: the result generalizes completely. The indicator of any set S with
μ(S) = 0 has zero Lebesgue integral. The key insight is that the Bochner
integral depends only on the a.e. behavior of the integrand, and 𝟙_S = 0
a.e. when μ(S) = 0.

## Proved (0 sorries, 0 axioms):

1. `indicator_ae_zero_of_null` — μ(S)=0 implies 𝟙_S = 0 a.e. [KEY LEMMA]
2. `integral_indicator_of_null` — ∫ 𝟙_S dμ = 0 for null S [MAIN THEOREM]
3. `integral_indicator_of_null_on_set` — ∫_T 𝟙_S dμ = 0 for null S, any T
4. `integral_mul_indicator_of_null` — ∫_T f·𝟙_S dμ = 0 for null S
5. `integral_on_null_set` — ∫_S f dμ = 0 for null S, any f
6. `integral_indicator_borel_null` — Lebesgue measure specialization
7. `integral_indicator_countable` — countable sets are null
8. `integral_indicator_finite` — finite sets are null
9. `integral_indicator_singleton` — single point {a} null
10. `integral_indicator_rationals` — Dirichlet function (OQ-01 special case)
11. `measure_iUnion_null_of_null` — countable union of null sets is null
12. `integral_indicator_iUnion_null` — union of null sets has zero indicator integral
13. `integral_on_iUnion_null_set` — integral over union of null sets is zero
14. `integral_congr_ae_null_change` — changing f on null set doesn't affect ∫
15. `integral_eq_zero_of_ae_zero` — a.e.-zero function has zero integral
-/

end LebesgueMeasureOQ01OQ03
