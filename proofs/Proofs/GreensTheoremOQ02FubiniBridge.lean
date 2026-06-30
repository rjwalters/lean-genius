/-
# Green's theorem OQ-02-OQ-02 — the Fubini reduction (iterated ⟷ 2D Lebesgue)

Research slug: `greens-theorem-oq-02-oq-02`.

## What this file supplies

The orientation-corrected axiom `GreensTheoremOQ02.greens_theorem_l1curl` now
concludes (after rewriting by its `hLineEq` hypothesis) the genuine rectangle
Green identity

    rectLineIntegral P Q a b c d
      = ∫ p in Set.Ioo a b ×ˢ Set.Ioo c d, curlF p ∂volume        (★)

whose right-hand side is a **2D Lebesgue integral over the open rectangle**.
The axiom-free C¹ theorem `GreensTheoremOQ01.greens_theorem_concrete` instead
proves

    rectLineIntegral P Q a b c d
      = rectDoubleIntegral (fun p => dQdx p - dPdy p) a b c d

where `rectDoubleIntegral f a b c d = ∫ y in c..d, ∫ x in a..b, f (x, y)` is an
**iterated interval integral**.  Every prior session of this problem listed the
missing connective between these two shapes as "step 3: the Fubini reduction",
but none had it as a stand-alone proven lemma.

This file proves exactly that connective, axiom-free:

    rectDoubleIntegral f a b c d
      = ∫ p in Set.Ioo a b ×ˢ Set.Ioo c d, f p ∂volume

for any `f` that is integrable on the rectangle, with `a ≤ b`, `c ≤ d`.  The
proof is pure Mathlib measure theory:

* `MeasureTheory.integral_prod_symm` (Fubini in the `y`-outer / `x`-inner order
  that matches `rectDoubleIntegral`),
* `MeasureTheory.Measure.prod_restrict` to turn the restricted product measure
  on `Ioo a b ×ˢ Ioo c d` into the product of the one-dimensional restrictions,
* `MeasureTheory.Measure.volume_eq_prod` (`rfl`) identifying `volume` on `ℝ × ℝ` with the
  product of the line measures,
* `intervalIntegral.integral_of_le` + `MeasureTheory.integral_Ioc_eq_integral_Ioo`
  to rewrite the two interval integrals as Lebesgue integrals over `Ioo`.

It is UNREGISTERED (not imported by `Proofs.lean`): it is supporting
infrastructure for the still-open C¹ discharge of the corrected axiom, not a new
gallery claim.  No axioms, no `sorry`.
-/
import Mathlib
import Proofs.GreensTheoremOQ01

open MeasureTheory

namespace GreensTheoremOQ02FubiniBridge

open GreensTheoremOQ01 (rectDoubleIntegral)

/-- **Interval integral over `[a,b]` equals the Lebesgue integral over the open
interval `Ioo a b`** (for `a ≤ b`, under `volume`, which has no atoms). -/
theorem intervalIntegral_eq_setIntegral_Ioo
    (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, g x) = ∫ x in Set.Ioo a b, g x ∂volume := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

/-- **The Fubini reduction.**  The iterated interval integral defining
`rectDoubleIntegral` (outer in `y`, inner in `x`) equals the 2D Lebesgue
integral of the same function over the open rectangle.

This is the precise connective between `GreensTheoremOQ01.greens_theorem_concrete`
(iterated form) and the right-hand side of the corrected
`GreensTheoremOQ02.greens_theorem_l1curl` axiom (2D-integral form `(★)` above). -/
theorem rectDoubleIntegral_eq_setIntegral
    (f : ℝ × ℝ → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hf : IntegrableOn f (Set.Ioo a b ×ˢ Set.Ioo c d) volume) :
    rectDoubleIntegral f a b c d
      = ∫ p in Set.Ioo a b ×ˢ Set.Ioo c d, f p ∂volume := by
  -- Fubini (y-outer / x-inner), over the open rectangle, in the product order.
  have hfubini :
      (∫ p in Set.Ioo a b ×ˢ Set.Ioo c d, f p ∂volume)
        = ∫ y in Set.Ioo c d, ∫ x in Set.Ioo a b, f (x, y) ∂volume ∂volume := by
    rw [show (volume : Measure (ℝ × ℝ))
          = (volume : Measure ℝ).prod (volume : Measure ℝ) from Measure.volume_eq_prod ℝ ℝ,
        ← Measure.prod_restrict]
    refine integral_prod_symm f ?_
    rw [Measure.prod_restrict]
    exact hf
  -- Unfold the iterated integral and convert each interval integral to `Ioo`.
  rw [rectDoubleIntegral, hfubini]
  have hx : ∀ y, (∫ x in a..b, f (x, y)) = ∫ x in Set.Ioo a b, f (x, y) ∂volume :=
    fun y => intervalIntegral_eq_setIntegral_Ioo (fun x => f (x, y)) hab
  simp_rw [hx]
  exact intervalIntegral_eq_setIntegral_Ioo
    (fun y => ∫ x in Set.Ioo a b, f (x, y) ∂volume) hcd

end GreensTheoremOQ02FubiniBridge
