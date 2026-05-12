/-
  Bochner Generalization of `intervalIntegral_swap`
  (greens-theorem-oq-01-oq-01-oq-02-oq-03)

  Parent slug: greens-theorem-oq-01-oq-01-oq-02 (verified, 0 sorries, 0 axioms)
  Question:    Do the three real-valued `intervalIntegral_swap` theorems
               generalize verbatim to a Banach codomain `E`?

  ## Answer (S1 OBSERVE audit): YES.

  Per the S1 OBSERVE audit (PR #17769):
  - Every Mathlib lemma the parent invokes
    (`MeasureTheory.integral_integral_swap`, `Measure.prod_mono`,
    `Measure.restrict_mono`, `integral_of_le`, `Integrable.mono_measure`)
    is already stated for Bochner-valued integrands
    (`E : NormedAddCommGroup`, `NormedSpace ℝ E`, `CompleteSpace E`).
  - The only ℝ-specific element of the parent's general-case proof is
    four `linarith` invocations in the sign analysis; `abel` replaces
    them directly (the underlying identity is additive-abelian, not
    order-theoretic).
  - The continuous case depends only on `Continuous.measurable` and
    `ContinuousOn.intervalIntegrable`, both of which are codomain-generic
    in Mathlib.

  ## Status of this file (S2 SCAFFOLD)

  Per the S1 plan in `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-03/state.md`:

  - `intervalIntegral_swap_of_le` for `f : ℝ → ℝ → E` — **fully proved**
    (smallest buildable instance demonstrating codomain genericity).
    The proof is a verbatim port of the parent's ordered-case script.
  - `intervalIntegral_swap` for `f : ℝ → ℝ → E` — `:= by sorry`
    (deferred to S3: 4-case sign analysis with `linarith → abel`).
  - `intervalIntegral_swap_of_continuous` for `f : ℝ → ℝ → E` — `:= by sorry`
    (deferred to S3: depends on the general case).

  Sorries: 2 (`intervalIntegral_swap`, `intervalIntegral_swap_of_continuous`).
  Axioms: 0.
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

open MeasureTheory intervalIntegral Set MeasureTheory.Measure

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 800000

namespace GreensTheoremOQ01OQ01OQ02OQ03

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ### Part I: Ordered Case (fully proved) -/

/-- **Fubini for Interval Integrals, Bochner generalization (ordered case)**.

For a Banach space `E` with `NormedSpace ℝ E` and `CompleteSpace E`, and
`f : ℝ → ℝ → E` with `a ≤ b` and `c ≤ d`, joint measurability + integrability
on `Icc a b ×ˢ Icc c d` implies the iterated Bochner integrals coincide.

This is a verbatim port of the parent file's `intervalIntegral_swap_of_le`
(real-valued case) — every Mathlib lemma used in the original proof is
already stated for Bochner integrands. -/
theorem intervalIntegral_swap_of_le {f : ℝ → ℝ → E}
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hf_meas : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hf_int : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  rw [integral_of_le hcd]
  conv_rhs => rw [integral_of_le hab]
  simp_rw [integral_of_le hab, integral_of_le hcd]
  have hf_ioc : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) :=
    hf_int.mono_measure (Measure.prod_mono
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
  exact (MeasureTheory.integral_integral_swap hf_ioc).symm

/-! ### Part II: Sign-Flip Helpers (Bochner-valued) -/

/-- Sign-flip: swapping bounds of an interval integral negates it.
Verbatim port of parent's `flip_bounds`. -/
private theorem flip_bounds_E (f : ℝ → E) (a b : ℝ) :
    ∫ x in a..b, f x = -(∫ x in b..a, f x) := by
  rw [integral_symm b a]

/-- Helper: `∫ x in a..b, -g x = -(∫ x in a..b, g x)` for Bochner integrals.
Verbatim port of parent's `neg_outside`. -/
private theorem neg_outside_E (a b : ℝ) (g : ℝ → E) :
    ∫ x in a..b, -g x = -(∫ x in a..b, g x) :=
  intervalIntegral.integral_neg g

/-! ### Part III: General Case (deferred to S3) -/

/-- **Fubini for Interval Integrals, Bochner generalization (general case)**.

For a Banach space `E` with `NormedSpace ℝ E` and `CompleteSpace E`, and
`f : ℝ → ℝ → E`, joint measurability + integrability on `uIcc a b ×ˢ uIcc c d`
implies the iterated Bochner integrals coincide, with no ordering hypothesis
on `(a, b)` or `(c, d)`.

**Proof strategy (deferred to S3)**: case-split on the four sign possibilities
of `(a ≤ b vs a > b)` × `(c ≤ d vs c > d)`. In each case, reduce to
`intervalIntegral_swap_of_le` via the sign-flip identity from `flip_bounds_E`,
combined with `neg_outside_E` to push the negations through the outer integral.
The four `linarith` steps from the parent's real-valued proof are replaced by
`abel` (the underlying identity is additive-abelian and codomain-generic).

The Aristotle companion `…Aristotle.lean` will expose `flip_bounds_E` and
`neg_outside_E` as routine targets in parallel. -/
theorem intervalIntegral_swap {f : ℝ → ℝ → E}
    (a b c d : ℝ)
    (hf_meas : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hf_int : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict (uIcc a b)).prod (volume.restrict (uIcc c d)))) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  sorry

/-! ### Part IV: Continuous Case (deferred to S3) -/

/-- **Fubini for Interval Integrals, Bochner generalization (continuous case)**.

For a Banach space `E` with `NormedSpace ℝ E` and `CompleteSpace E`, and
a *continuous* function `f : ℝ × ℝ → E`, the iterated interval integrals on
any `(a, b) × (c, d)` rectangle coincide, with no measurability or
integrability hypotheses — both are automatic from continuity on the compact
rectangle.

**Proof strategy (deferred to S3)**: apply `intervalIntegral_swap` (above),
extracting measurability from `Continuous.measurable` and integrability from
`ContinuousOn.integrableOn_compact` applied to the closed rectangle.
Both helpers are codomain-generic in Mathlib. -/
theorem intervalIntegral_swap_of_continuous {f : ℝ → ℝ → E}
    (a b c d : ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  sorry

end GreensTheoremOQ01OQ01OQ02OQ03
