/-
  Standalone Interval Integral Swap (greens-theorem-oq-01-oq-01-oq-02)

  Open Question from greens-theorem-oq-01-oq-01:
  "Does Mathlib contain (or could it be contributed) a version of
  `intervalIntegral_swap` as a standalone lemma, avoiding the need
  for each application to reimplement the Ioc/Icc conversion?"

  ## Answer: No standalone version exists in Mathlib — we prove one here.

  Mathlib (as of mathlib4 rev 2df2f015) has `MeasureTheory.integral_integral_swap`
  (Fubini for Lebesgue integrals) but no `intervalIntegral_swap`. Every use
  of interval integral Fubini must reimplement the Ioc/Icc bridge.

  This file provides three versions:
  1. **Ordered** (a ≤ b, c ≤ d): direct from Fubini + Ioc bridge
  2. **General** (any a, b, c, d): uses sign-flip ∫ x in a..b = -∫ x in b..a
  3. **Continuous**: measurability and integrability are automatic

  Sorries: 0
  Axioms: 0
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

open MeasureTheory intervalIntegral Set MeasureTheory.Measure

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 800000

namespace GreensTheoremOQ01OQ01OQ02

/-! ### Part I: Ordered Case -/

/-- **Fubini for Interval Integrals (Ordered case, a ≤ b, c ≤ d)**

    Converts to Lebesgue integrals via `integral_of_le`, applies
    `MeasureTheory.integral_integral_swap`, and converts back.
    The `hFubini` hypothesis from GreensTheoremOQ01 is provable under
    standard measurability + integrability — it is NOT a mathematical axiom.
-/
theorem intervalIntegral_swap_of_le {f : ℝ → ℝ → ℝ}
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

/-! ### Part II: General Version -/

/-- Sign-flip: swapping bounds of an interval integral negates it. -/
private theorem flip_bounds (f : ℝ → ℝ) (a b : ℝ) :
    ∫ x in a..b, f x = -(∫ x in b..a, f x) := by
  rw [integral_symm b a]

/-- Helper: `∫ x in a..b, -g x = -(∫ x in a..b, g x)` -/
private theorem neg_outside (a b : ℝ) (g : ℝ → ℝ) :
    ∫ x in a..b, -g x = -(∫ x in a..b, g x) :=
  intervalIntegral.integral_neg g

/-- **Fubini for Interval Integrals (General)**

    No ordering assumption on a, b, c, d. Uses `uIcc` for integrability.

    **This lemma does NOT exist in Mathlib** (as of mathlib4 rev 2df2f015).
    The proof reduces all 4 orderings of (a,b) and (c,d) to the ordered case
    by applying the sign-flip identity `∫ x in a..b = -∫ x in b..a`.
-/
theorem intervalIntegral_swap {f : ℝ → ℝ → ℝ}
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
      -- A = ∫ y in c..d, ∫ x in a..b, f x y
      -- B = ∫ y in d..c, ∫ x in a..b, f x y
      -- C = ∫ x in a..b, ∫ y in d..c, f x y
      -- D = ∫ x in a..b, ∫ y in c..d, f x y (goal RHS)
      -- A = -B  (flip_bounds c d)
      -- B = C   (ordered swap)
      -- C = -D  (pull neg out of inner integral)
      -- Therefore A = D
      have hAB : ∫ y in c..d, ∫ x in a..b, f x y =
            -(∫ y in d..c, ∫ x in a..b, f x y) :=
        flip_bounds (fun y => ∫ x in a..b, f x y) c d
      have hBC : ∫ y in d..c, ∫ x in a..b, f x y =
            ∫ x in a..b, ∫ y in d..c, f x y :=
        intervalIntegral_swap_of_le a b d c hab hdc hf_meas int2
      have hinner : ∀ x, ∫ y in d..c, f x y = -(∫ y in c..d, f x y) :=
        fun x => flip_bounds (f x) d c
      have hCD : ∫ x in a..b, ∫ y in d..c, f x y =
            -(∫ x in a..b, ∫ y in c..d, f x y) := by
        simp_rw [hinner]
        exact neg_outside a b (fun x => ∫ y in c..d, f x y)
      linarith
  · -- b < a
    rcases le_or_lt c d with hcd | hcd
    · -- Case 3: b < a, c ≤ d → flip inner
      have hba := le_of_lt hab
      have int3 : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
          ((volume.restrict (Icc b a)).prod (volume.restrict (Icc c d))) := by
        rwa [uIcc_comm a b, uIcc_of_le hba, uIcc_of_le hcd] at hf_int
      -- A = ∫ y in c..d, ∫ x in a..b, f x y
      -- B = ∫ y in c..d, ∫ x in b..a, f x y
      -- C = ∫ x in b..a, ∫ y in c..d, f x y
      -- D = ∫ x in a..b, ∫ y in c..d, f x y (goal RHS)
      -- A = -B  (flip inner for each y)
      -- B = C   (ordered swap)
      -- C = -D  (flip outer bounds)
      have hinner_ba : ∀ y, ∫ x in a..b, f x y = -(∫ x in b..a, f x y) :=
        fun y => flip_bounds (fun x => f x y) a b
      have hAB : ∫ y in c..d, ∫ x in a..b, f x y =
            -(∫ y in c..d, ∫ x in b..a, f x y) := by
        simp_rw [hinner_ba]
        exact neg_outside c d (fun y => ∫ x in b..a, f x y)
      have hBC : ∫ y in c..d, ∫ x in b..a, f x y =
            ∫ x in b..a, ∫ y in c..d, f x y :=
        intervalIntegral_swap_of_le b a c d hba hcd hf_meas int3
      have hCD : ∫ x in b..a, ∫ y in c..d, f x y =
            -(∫ x in a..b, ∫ y in c..d, f x y) :=
        flip_bounds (fun x => ∫ y in c..d, f x y) b a
      linarith
    · -- Case 4: b < a, d < c → flip both
      have hba := le_of_lt hab
      have hdc := le_of_lt hcd
      have int4 : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
          ((volume.restrict (Icc b a)).prod (volume.restrict (Icc d c))) := by
        rwa [uIcc_comm a b, uIcc_of_le hba, uIcc_comm c d, uIcc_of_le hdc] at hf_int
      -- A = -B (inner flip), B = -C (outer flip), C = D' (swap), D' = -D'' (inner flip back),
      -- D'' = -D (outer flip back) → A = D via four sign cancellations
      have hinner_ba : ∀ y, ∫ x in a..b, f x y = -(∫ x in b..a, f x y) :=
        fun y => flip_bounds (fun x => f x y) a b
      have hAB : ∫ y in c..d, ∫ x in a..b, f x y =
            -(∫ y in c..d, ∫ x in b..a, f x y) := by
        simp_rw [hinner_ba]; exact neg_outside c d (fun y => ∫ x in b..a, f x y)
      have hBC : ∫ y in c..d, ∫ x in b..a, f x y =
            -(∫ y in d..c, ∫ x in b..a, f x y) :=
        flip_bounds (fun y => ∫ x in b..a, f x y) c d
      have hCD : ∫ y in d..c, ∫ x in b..a, f x y =
            ∫ x in b..a, ∫ y in d..c, f x y :=
        intervalIntegral_swap_of_le b a d c hba hdc hf_meas int4
      have hinner_dc : ∀ x, ∫ y in d..c, f x y = -(∫ y in c..d, f x y) :=
        fun x => flip_bounds (f x) d c
      have hDE : ∫ x in b..a, ∫ y in d..c, f x y =
            -(∫ x in b..a, ∫ y in c..d, f x y) := by
        simp_rw [hinner_dc]; exact neg_outside b a (fun x => ∫ y in c..d, f x y)
      have hEF : ∫ x in b..a, ∫ y in c..d, f x y =
            -(∫ x in a..b, ∫ y in c..d, f x y) :=
        flip_bounds (fun x => ∫ y in c..d, f x y) b a
      linarith

/-! ### Part III: Continuous Case -/

/-- **Fubini for Interval Integrals (Continuous)**

    For continuous f, measurability and integrability on the compact rectangle
    `uIcc a b × uIcc c d` are automatic. No ordering required.
-/
theorem intervalIntegral_swap_of_continuous {f : ℝ → ℝ → ℝ}
    (a b c d : ℝ) (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  apply intervalIntegral_swap a b c d hf.measurable
  have hcpt : IsCompact (uIcc a b ×ˢ uIcc c d) :=
    isCompact_uIcc.prod isCompact_uIcc
  have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (uIcc a b ×ˢ uIcc c d) volume :=
    hf.continuousOn.integrableOn_compact hcpt
  rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint

/-! ### Part IV: Application to Green's Theorem -/

/-- For any continuous ∂P/∂y, the Fubini hypothesis in Green's theorem is satisfied. -/
theorem greens_theorem_fubini_discharged
    (dPdy : ℝ × ℝ → ℝ) (a b c d : ℝ) (h : Continuous dPdy) :
    ∫ y in c..d, ∫ x in a..b, dPdy (x, y) =
    ∫ x in a..b, ∫ y in c..d, dPdy (x, y) :=
  intervalIntegral_swap_of_continuous a b c d
    (h.comp (continuous_prod_mk.mpr ⟨continuous_fst, continuous_snd⟩))

/-! ### Summary

## Research Finding

Mathlib (mathlib4 rev 2df2f015) does NOT contain a standalone `intervalIntegral_swap`.

## What We Proved (0 sorries, 0 axioms)

| Theorem | Hypotheses | Note |
|---------|------------|------|
| `intervalIntegral_swap_of_le` | a ≤ b, c ≤ d, Icc integrability | Core result |
| `intervalIntegral_swap` | any a,b,c,d, uIcc integrability | Not in Mathlib |
| `intervalIntegral_swap_of_continuous` | any a,b,c,d, continuous f | Not in Mathlib |
| `greens_theorem_fubini_discharged` | continuous dPdy | Application |

## Key Technique

The general version reduces to the ordered case by noting that
`∫ x in a..b = -∫ x in b..a` (sign convention of interval integrals).
In each of the 4 orderings of (a≤b or b<a) × (c≤d or d<c), the sign
changes cancel appropriately in the equality.

## Mathlib Contribution Path

Target: `Mathlib.MeasureTheory.Integral.IntervalIntegral`
Suggested lemma: `intervalIntegral.swap` or `intervalIntegral.integral_comm`
-/

end GreensTheoremOQ01OQ01OQ02
