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

  ## Status of this file (S3 ACT)

  Per the S2 plan in `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-03/state.md`:

  - `intervalIntegral_swap_of_le` for `f : ℝ → ℝ → E` — **fully proved** (S2).
  - `intervalIntegral_swap` for `f : ℝ → ℝ → E` — **fully proved** (S3 ACT).
    Four-case sign analysis ported verbatim from the parent; `linarith` is
    replaced by explicit `rw + neg_neg` rewrites (the underlying identity is
    additive-abelian, not order-theoretic).
  - `intervalIntegral_swap_of_continuous` for `f : ℝ → ℝ → E` — **fully proved**
    (S3 ACT). Reduces to the general case via `Continuous.measurable` and
    `ContinuousOn.integrableOn_compact`, both Bochner-generic in Mathlib.

  Sorries: 0.
  Axioms: 0.
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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

/-! ### Part III: General Case (S3 proven) -/

/-- **Fubini for Interval Integrals, Bochner generalization (general case)**.

For a Banach space `E` with `NormedSpace ℝ E` and `CompleteSpace E`, and
`f : ℝ → ℝ → E`, joint measurability + integrability on `uIcc a b ×ˢ uIcc c d`
implies the iterated Bochner integrals coincide, with no ordering hypothesis
on `(a, b)` or `(c, d)`.

**Proof.** Case-split on the four sign possibilities of `(a ≤ b vs a > b)` ×
`(c ≤ d vs c > d)`. In each case, reduce to `intervalIntegral_swap_of_le` via
the sign-flip identity `flip_bounds_E`, combined with `neg_outside_E` to push
negations through the outer integral. The parent file's four `linarith` calls
are replaced by `rw + neg_neg` rewrites (the underlying identity is
additive-abelian and codomain-generic). -/
theorem intervalIntegral_swap {f : ℝ → ℝ → E}
    (a b c d : ℝ)
    (hf_meas : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hf_int : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict (uIcc a b)).prod (volume.restrict (uIcc c d)))) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  rcases le_or_lt a b with hab | hab
  · -- a ≤ b
    rcases le_or_lt c d with hcd | hcd
    · -- Case 1: a ≤ b, c ≤ d → direct
      exact intervalIntegral_swap_of_le a b c d hab hcd hf_meas
        (by rwa [uIcc_of_le hab, uIcc_of_le hcd] at hf_int)
    · -- Case 2: a ≤ b, d < c → flip outer
      have hdc := le_of_lt hcd
      have int2 : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
          ((volume.restrict (Icc a b)).prod (volume.restrict (Icc d c))) := by
        rwa [uIcc_of_le hab, uIcc_comm c d, uIcc_of_le hdc] at hf_int
      have hAB : ∫ y in c..d, ∫ x in a..b, f x y =
            -(∫ y in d..c, ∫ x in a..b, f x y) :=
        flip_bounds_E (fun y => ∫ x in a..b, f x y) c d
      have hBC : ∫ y in d..c, ∫ x in a..b, f x y =
            ∫ x in a..b, ∫ y in d..c, f x y :=
        intervalIntegral_swap_of_le a b d c hab hdc hf_meas int2
      have hinner : ∀ x, ∫ y in d..c, f x y = -(∫ y in c..d, f x y) :=
        fun x => flip_bounds_E (f x) d c
      have hCD : ∫ x in a..b, ∫ y in d..c, f x y =
            -(∫ x in a..b, ∫ y in c..d, f x y) := by
        simp_rw [hinner]
        exact neg_outside_E a b (fun x => ∫ y in c..d, f x y)
      rw [hAB, hBC, hCD, neg_neg]
  · -- b < a
    rcases le_or_lt c d with hcd | hcd
    · -- Case 3: b < a, c ≤ d → flip inner
      have hba := le_of_lt hab
      have int3 : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
          ((volume.restrict (Icc b a)).prod (volume.restrict (Icc c d))) := by
        rwa [uIcc_comm a b, uIcc_of_le hba, uIcc_of_le hcd] at hf_int
      have hinner_ba : ∀ y, ∫ x in a..b, f x y = -(∫ x in b..a, f x y) :=
        fun y => flip_bounds_E (fun x => f x y) a b
      have hAB : ∫ y in c..d, ∫ x in a..b, f x y =
            -(∫ y in c..d, ∫ x in b..a, f x y) := by
        simp_rw [hinner_ba]
        exact neg_outside_E c d (fun y => ∫ x in b..a, f x y)
      have hBC : ∫ y in c..d, ∫ x in b..a, f x y =
            ∫ x in b..a, ∫ y in c..d, f x y :=
        intervalIntegral_swap_of_le b a c d hba hcd hf_meas int3
      have hCD : ∫ x in b..a, ∫ y in c..d, f x y =
            -(∫ x in a..b, ∫ y in c..d, f x y) :=
        flip_bounds_E (fun x => ∫ y in c..d, f x y) b a
      rw [hAB, hBC, hCD, neg_neg]
    · -- Case 4: b < a, d < c → flip both
      have hba := le_of_lt hab
      have hdc := le_of_lt hcd
      have int4 : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
          ((volume.restrict (Icc b a)).prod (volume.restrict (Icc d c))) := by
        rwa [uIcc_comm a b, uIcc_of_le hba, uIcc_comm c d, uIcc_of_le hdc] at hf_int
      have hinner_ba : ∀ y, ∫ x in a..b, f x y = -(∫ x in b..a, f x y) :=
        fun y => flip_bounds_E (fun x => f x y) a b
      have hAB : ∫ y in c..d, ∫ x in a..b, f x y =
            -(∫ y in c..d, ∫ x in b..a, f x y) := by
        simp_rw [hinner_ba]; exact neg_outside_E c d (fun y => ∫ x in b..a, f x y)
      have hBC : ∫ y in c..d, ∫ x in b..a, f x y =
            -(∫ y in d..c, ∫ x in b..a, f x y) :=
        flip_bounds_E (fun y => ∫ x in b..a, f x y) c d
      have hCD : ∫ y in d..c, ∫ x in b..a, f x y =
            ∫ x in b..a, ∫ y in d..c, f x y :=
        intervalIntegral_swap_of_le b a d c hba hdc hf_meas int4
      have hinner_dc : ∀ x, ∫ y in d..c, f x y = -(∫ y in c..d, f x y) :=
        fun x => flip_bounds_E (f x) d c
      have hDE : ∫ x in b..a, ∫ y in d..c, f x y =
            -(∫ x in b..a, ∫ y in c..d, f x y) := by
        simp_rw [hinner_dc]; exact neg_outside_E b a (fun x => ∫ y in c..d, f x y)
      have hEF : ∫ x in b..a, ∫ y in c..d, f x y =
            -(∫ x in a..b, ∫ y in c..d, f x y) :=
        flip_bounds_E (fun x => ∫ y in c..d, f x y) b a
      rw [hAB, hBC, hCD, hDE, hEF]
      simp only [neg_neg]

/-! ### Part IV: Continuous Case (S3 proven) -/

/-- **Fubini for Interval Integrals, Bochner generalization (continuous case)**.

For a Banach space `E` with `NormedSpace ℝ E` and `CompleteSpace E`, and
a *continuous* function `f : ℝ × ℝ → E`, the iterated interval integrals on
any `(a, b) × (c, d)` rectangle coincide, with no measurability or
integrability hypotheses — both are automatic from continuity on the compact
rectangle.

**Proof.** Apply `intervalIntegral_swap` after extracting measurability from
`Continuous.measurable` and integrability from
`ContinuousOn.integrableOn_compact` on the compact rectangle
`uIcc a b ×ˢ uIcc c d`. Both helpers are codomain-generic in Mathlib. -/
theorem intervalIntegral_swap_of_continuous {f : ℝ → ℝ → E}
    (a b c d : ℝ)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  apply intervalIntegral_swap a b c d hf.measurable
  have hcpt : IsCompact (uIcc a b ×ˢ uIcc c d) :=
    isCompact_uIcc.prod isCompact_uIcc
  have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (uIcc a b ×ˢ uIcc c d) volume :=
    hf.continuousOn.integrableOn_compact hcpt
  rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint

end GreensTheoremOQ01OQ01OQ02OQ03
