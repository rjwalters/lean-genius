/-
Fundamental Theorem of Calculus — Banach-Valued Generalization (OQ-04)

## Research Question

The parent `FundamentalTheoremCalculus.lean` proves both FTC parts for ℝ → ℝ functions.
OQ-04 asks: can we formalize both parts of the FTC for vector-valued functions
F : ℝ → E where E is a Banach space, using the Bochner integral?

## Answer

YES. Mathlib's FTC machinery in `IntervalIntegral.FundThmCalculus` is already
stated for arbitrary Banach spaces E : Type* with [NormedAddCommGroup E] [NormedSpace ℝ E].
The ℝ → ℝ case in the parent file is a special instance of the general theory.

Main results in this file:
- `ftc2_banach`: Second FTC for Bochner integrals (∫ F' = F b - F a)
- `ftc1_banach`: First FTC for Bochner integrals (d/dx ∫_a^x f = f(x))
- `antiderivative_banach`: Antiderivative characterization in Banach spaces
- `ftc2_product`: Concrete instance for ℝ × ℝ-valued functions
- `ftc2_pi`: Concrete instance for (Fin n → ℝ)-valued functions
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

open MeasureTheory Set Filter Topology intervalIntegral

namespace FTCBanach

/-! ## Part 1: Second FTC for Banach-Valued Functions (Bochner Integral) -/

/-- **Second FTC for Banach spaces**: If F : ℝ → E is continuous on [a, b]
    and has derivative f on (a, b), and f is Bochner integrable, then
    ∫ t in a..b, f t ∂μ = F b - F a.

    This is the Banach-space generalization of the classical FTC-2.
    The proof is immediate from Mathlib's `integral_eq_sub_of_hasDerivAt_of_le`,
    which is already stated for arbitrary Banach spaces. -/
theorem ftc2_banach {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F f : ℝ → E} {a b : ℝ}
    (hab : a ≤ b)
    (hF_cont : ContinuousOn F (Icc a b))
    (hF_deriv : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x)
    (hf_int : IntervalIntegrable f volume a b) :
    ∫ t in a..b, f t = F b - F a :=
  integral_eq_sub_of_hasDerivAt_of_le hab hF_cont hF_deriv hf_int

/-- **Second FTC (general endpoints)**: The version without the `a ≤ b` assumption.
    Works for any endpoints; uses `uIcc` for the continuity domain. -/
theorem ftc2_banach_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F f : ℝ → E} {a b : ℝ}
    (hF_cont : ContinuousOn F (uIcc a b))
    (hF_deriv : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt F (f x) (Ioi x) x)
    (hf_int : IntervalIntegrable f volume a b) :
    ∫ t in a..b, f t = F b - F a :=
  integral_eq_sub_of_hasDeriv_right hF_cont hF_deriv hf_int

/-! ## Part 2: First FTC for Banach-Valued Functions -/

/-- **First FTC for Banach spaces**: If f : ℝ → E is continuous at b and
    integrable on a..b, then the integral function x ↦ ∫ t in a..x, f t
    has derivative f(b) at b.

    Again, Mathlib's `integral_hasDerivAt_right` works for all Banach E. -/
theorem ftc1_banach {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {a b : ℝ}
    (hf_int : IntervalIntegrable f volume a b)
    (hf_meas : StronglyMeasurableAtFilter f (𝓝 b) volume)
    (hf_cont : ContinuousAt f b) :
    HasDerivAt (fun x => ∫ t in a..x, f t) (f b) b :=
  integral_hasDerivAt_right hf_int hf_meas hf_cont

/-- Under global continuity, the first FTC holds everywhere. -/
theorem ftc1_banach_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} (hf : Continuous f) (a x : ℝ) :
    HasDerivAt (fun y => ∫ t in a..y, f t) (f x) x :=
  ftc1_banach
    (hf.intervalIntegrable a x)
    (hf.stronglyMeasurableAtFilter volume (𝓝 x))
    hf.continuousAt

/-! ## Antiderivative Structure in Banach Spaces -/

/-- An **antiderivative** of a Banach-valued function f is any F with F' = f. -/
def IsAntiderivativeBanach {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F f : ℝ → E) : Prop :=
  ∀ x, HasDerivAt F (f x) x

/-- The integral function is an antiderivative of any continuous Banach-valued f. -/
theorem integral_is_antiderivative_banach {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} (hf : Continuous f) (a : ℝ) :
    IsAntiderivativeBanach (fun x => ∫ t in a..x, f t) f :=
  fun x => ftc1_banach_continuous hf a x

/-- **Antiderivatives differ by a constant** (Banach version):
    If F and G are both antiderivatives of f : ℝ → E, then F - G is constant. -/
theorem banach_antiderivatives_differ_by_constant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G f : ℝ → E}
    (hF : IsAntiderivativeBanach F f) (hG : IsAntiderivativeBanach G f) :
    ∃ c : E, ∀ x, F x - G x = c := by
  use F 0 - G 0
  intro x
  have hFG : ∀ y, HasDerivAt (fun z => F z - G z) 0 y := by
    intro y
    have := (hF y).sub (hG y)
    simp at this
    exact this
  have hdiff : Differentiable ℝ (fun z => F z - G z) :=
    fun z => (hFG z).differentiableAt
  have hderiv : ∀ z, deriv (fun z => F z - G z) z = 0 :=
    fun z => (hFG z).deriv
  exact (is_const_of_deriv_eq_zero hdiff hderiv x 0).symm ▸ rfl

/-! ## Concrete Instances -/

/-- **FTC-2 for ℝ × ℝ**: The product of two real-valued functions.
    Illustrates the theorem with a concrete Banach space. -/
theorem ftc2_product {F f : ℝ → ℝ × ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hF_cont : ContinuousOn F (Icc a b))
    (hF_deriv : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x)
    (hf_int : IntervalIntegrable f volume a b) :
    ∫ t in a..b, f t = F b - F a :=
  ftc2_banach hab hF_cont hF_deriv hf_int

/-- **FTC-2 for Fin n → ℝ**: Vector-valued functions into ℝⁿ.
    The FTC holds componentwise for all coordinate functions simultaneously. -/
theorem ftc2_pi {n : ℕ} {F f : ℝ → (Fin n → ℝ)} {a b : ℝ}
    (hab : a ≤ b)
    (hF_cont : ContinuousOn F (Icc a b))
    (hF_deriv : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x)
    (hf_int : IntervalIntegrable f volume a b) :
    ∫ t in a..b, f t = F b - F a :=
  ftc2_banach hab hF_cont hF_deriv hf_int

/-! ## Key Insight: Why the Proof Compiles Unchanged

The proof of `ftc2_banach` is identical to `ftc_part2` in the parent file —
only the types change. This reflects a deep fact: Mathlib's FTC theorems are
stated polymorphically over any Banach space E with:

  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

The Bochner integral ∫ t, f t for f : ℝ → E is defined for L¹(ℝ, E) functions,
and the FTC holds in this generality. No new proof techniques are needed.

The real contribution of the FTC in Banach spaces is the integration theory:
proving that reasonable Banach-valued functions are Bochner integrable, and
that the Bochner integral has the expected linearity and norm estimates.
These are already in Mathlib's `Bochner.Basic` and `Bochner.L1`.
-/

/-- Summary: The FTC in Banach spaces reduces to the real-valued case via the
    type class machinery. Both FTC-1 and FTC-2 hold in full generality for
    continuous (resp. a.e. differentiable) Bochner integrable functions. -/
theorem ftc_banach_summary :
    (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
       (F f : ℝ → E) (a b : ℝ),
       a ≤ b →
       ContinuousOn F (Icc a b) →
       (∀ x ∈ Ioo a b, HasDerivAt F (f x) x) →
       IntervalIntegrable f volume a b →
       ∫ t in a..b, f t = F b - F a) := by
  intro E _ _ _ F f a b hab hcont hderiv hint
  exact ftc2_banach hab hcont hderiv hint

end FTCBanach
