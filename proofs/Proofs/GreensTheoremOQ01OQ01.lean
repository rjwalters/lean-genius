/-
  Fubini's Theorem for Iterated Interval Integrals

  Proves the Fubini hypothesis in GreensTheoremOQ01.lean:
    ∫ y in c..d, ∫ x in a..b, f(x,y) = ∫ x in a..b, ∫ y in c..d, f(x,y)

  This connects Mathlib's abstract Fubini theorem (for measure-theoretic
  integrals on product spaces) to the concrete iterated intervalIntegral
  used in the Green's theorem formalization.

  Key Mathlib tools:
  - MeasureTheory.integral_integral_swap (Fubini for Lebesgue integrals)
  - intervalIntegral.integral_of_le (converting interval → set integral)
  - Measure.prod_restrict (product of restricted measures)

  Axioms: 0
  Sorries: 0
-/
import Mathlib

namespace GreensTheoremOQ01OQ01

open MeasureTheory intervalIntegral Set Filter Topology

-- ═══════════════════════════════════════════════════
-- Part I: Fubini for Interval Integrals
-- ═══════════════════════════════════════════════════

/-- **Fubini's Theorem for Iterated Interval Integrals.**

    Under suitable integrability conditions, iterated interval integrals
    can be swapped:
      ∫ y in c..d, ∫ x in a..b, f(x,y) = ∫ x in a..b, ∫ y in c..d, f(x,y)

    This is the concrete form needed for Green's theorem (OQ-01).

    The proof converts interval integrals to set integrals on Ioc,
    applies Mathlib's Fubini theorem (integral_integral_swap), and
    converts back. The key insight is that ∫ x in a..b = ∫ x in Ioc a b
    for a ≤ b, and set_integral is just integral with restricted measure.
-/
theorem intervalIntegral_swap {f : ℝ → ℝ → ℝ}
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hf_meas : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hf_int : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d)))) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  -- Step 1: Convert outer interval integrals to set integrals on Ioc
  rw [intervalIntegral.integral_of_le hcd]
  conv_rhs => rw [intervalIntegral.integral_of_le hab]
  -- Step 2: Convert inner interval integrals to set integrals on Ioc
  simp_rw [intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le hcd]
  -- Now both sides are set_integrals:
  -- LHS: ∫ y in Ioc c d, ∫ x in Ioc a b, f x y
  -- RHS: ∫ x in Ioc a b, ∫ y in Ioc c d, f x y
  -- These are iterated integrals with restricted measures:
  -- LHS = ∫ y ∂(vol.restrict (Ioc c d)), ∫ x ∂(vol.restrict (Ioc a b)), f x y
  -- RHS = ∫ x ∂(vol.restrict (Ioc a b)), ∫ y ∂(vol.restrict (Ioc c d)), f x y
  -- Step 3: Derive integrability on Ioc product from Icc integrability
  have hf_int' : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc c d))) := by
    apply hf_int.mono_measure
    simp only [Measure.prod_restrict]
    exact Measure.restrict_mono
        (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self) le_rfl
  -- Step 4: Apply Fubini (integral_integral_swap)
  -- integral_integral_swap: ∫ x ∂μ, ∫ y ∂ν, g x y = ∫ y ∂ν, ∫ x ∂μ, g x y
  -- With μ = vol.restrict (Ioc a b), ν = vol.restrict (Ioc c d), g = f:
  -- RHS = ∫ x ∂μ, ∫ y ∂ν, f x y (our RHS after conversion)
  -- Fubini gives: RHS = ∫ y ∂ν, ∫ x ∂μ, f x y = LHS after conversion
  exact (MeasureTheory.integral_integral_swap hf_int').symm

-- ═══════════════════════════════════════════════════
-- Part II: Application to Green's Theorem
-- ═══════════════════════════════════════════════════

/-- The `hFubini` hypothesis from `GreensTheoremOQ01.greens_theorem_concrete`
    is a special case of `intervalIntegral_swap` applied to `dPdy`.

    Given:
    - dPdy is measurable
    - dPdy is integrable on [a,b] × [c,d]
    - a ≤ b, c ≤ d

    We can derive:
    ∫ y in c..d, ∫ x in a..b, dPdy (x, y) = ∫ x in a..b, ∫ y in c..d, dPdy (x, y)

    This eliminates the `hFubini` hypothesis, making Green's theorem fully proved
    from Mathlib (under measurability + integrability, which are standard
    regularity conditions for Green's theorem anyway). -/
theorem greens_fubini_eliminated
    (dPdy : ℝ × ℝ → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hf_meas : Measurable dPdy)
    (hf_int : Integrable dPdy
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d)))) :
    ∫ y in c..d, ∫ x in a..b, dPdy (x, y) =
    ∫ x in a..b, ∫ y in c..d, dPdy (x, y) :=
  intervalIntegral_swap a b c d hab hcd hf_meas hf_int

-- ═══════════════════════════════════════════════════
-- Part III: Sufficient Conditions for Integrability
-- ═══════════════════════════════════════════════════

/-- For continuous functions, the integrability condition is automatic
    on compact rectangles. This shows the Fubini hypothesis holds
    whenever dPdy is continuous (a common assumption for Green's theorem). -/
theorem fubini_of_continuous {f : ℝ × ℝ → ℝ}
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hf : Continuous f) :
    ∫ y in c..d, ∫ x in a..b, f (x, y) = ∫ x in a..b, ∫ y in c..d, f (x, y) := by
  apply intervalIntegral_swap a b c d hab hcd hf.measurable
  -- Continuous functions are integrable on compact sets
  -- Icc a b × Icc c d is compact (product of compact intervals)
  have hcpt : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) :=
    isCompact_Icc.prod isCompact_Icc
  -- f is integrable on the compact rectangle
  have hint : IntegrableOn f (Set.Icc a b ×ˢ Set.Icc c d) volume :=
    hf.continuousOn.integrableOn_compact hcpt
  -- Convert: IntegrableOn f (S ×ˢ T) vol = Integrable f (vol.restrict S).prod (vol.restrict T)
  -- Measure.prod_restrict: (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)
  -- volume (ℝ × ℝ) = volume (ℝ) × volume (ℝ) definitionally
  have : Integrable f ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc c d))) := by
    rw [Measure.prod_restrict]; exact hint
  exact this

/-- Spelling out: for C¹ vector fields (P, Q), the Fubini hypothesis
    in Green's theorem is always satisfied. -/
theorem greens_fubini_for_C1
    (P : ℝ × ℝ → ℝ) (dPdy : ℝ × ℝ → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hPdy_cont : Continuous dPdy) :
    ∫ y in c..d, ∫ x in a..b, dPdy (x, y) =
    ∫ x in a..b, ∫ y in c..d, dPdy (x, y) :=
  fubini_of_continuous a b c d hab hcd hPdy_cont

-- ═══════════════════════════════════════════════════
-- Summary
-- ═══════════════════════════════════════════════════
/-
## Research Outcome

The `hFubini` hypothesis in Green's theorem (OQ-01) CAN be eliminated.

**Proof complete**: All sorries resolved. The key tool is Mathlib's
`MeasureTheory.integral_integral_swap` (Fubini for Lebesgue integrals),
combined with `intervalIntegral.integral_of_le` to convert between
interval integrals and set integrals.

**For C¹ vector fields** (standard for Green's theorem), the
measurability and integrability hypotheses are automatic via
`Continuous.measurable` and `ContinuousOn.integrableOn_compact`.
-/

end GreensTheoremOQ01OQ01
