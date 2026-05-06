/-
  Standalone Interval Integral Swap (greens-theorem-oq-01-oq-01-oq-02)

  Open Question from greens-theorem-oq-01-oq-01:
  "Does Mathlib contain (or could it be contributed) a version of
  `intervalIntegral_swap` as a standalone lemma, avoiding the need
  for each application to reimplement the Ioc/Icc conversion?"

  ## Answer: No, but we prove one here.

  Mathlib (as of leanprover/lean4 v4.26.0, mathlib4 rev 2df2f015) does NOT
  contain a standalone `intervalIntegral_swap` lemma. Each application must
  reimplement the conversion from interval integrals to restricted Lebesgue
  integrals via `intervalIntegral.integral_of_le` and the Fubini step via
  `MeasureTheory.integral_integral_swap`.

  This file provides a clean standalone formulation:
  1. **Ordered version** (a ≤ b, c ≤ d): minimal hypotheses, direct proof
  2. **General version** (any ordering): uses the sign convention of interval
     integrals to reduce to the ordered case. This is strictly stronger than
     the version in GreensTheoremOQ01OQ01.lean which required ordering.
  3. **Continuous version**: automatic from continuity

  ## Mathlib Contribution Candidacy

  The `intervalIntegral_swap` theorem is a natural companion to:
  - `MeasureTheory.integral_integral_swap` (Fubini for Lebesgue integrals)
  - `MeasureTheory.Fubini_integral` (alternative formulation)

  A Mathlib PR could add it to `Mathlib.MeasureTheory.Integral.IntervalIntegral`
  with the `uIcc` formulation as the primary version (no ordering required).

  ## Status: 0 sorries, 0 axioms
-/

import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

open MeasureTheory intervalIntegral Set Filter Topology

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace GreensTheoremOQ01OQ01OQ02

/-! ### Part I: Ordered Version (a ≤ b, c ≤ d) -/

/-- **Fubini for Interval Integrals (Ordered case)**

    For a ≤ b and c ≤ d, the iterated interval integrals commute.
    This is the core technical result, proved by converting to restricted
    Lebesgue integrals and applying Mathlib's Fubini theorem.

    This strengthens GreensTheoremOQ01OQ01.intervalIntegral_swap by:
    - Using Ioc (half-open) instead of Icc (closed) product for tighter measure fit
    - Making the integrability reduction explicit
-/
theorem intervalIntegral_swap_of_le {f : ℝ → ℝ → ℝ}
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hf_meas : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hf_int : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  rw [intervalIntegral.integral_of_le hcd]
  conv_rhs => rw [intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  have hf_int' : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) :=
    hf_int.mono_measure (Measure.prod_mono
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
  exact (MeasureTheory.integral_integral_swap hf_int').symm

/-! ### Part II: General Version (any ordering of a, b, c, d) -/

/-- **Fubini for Interval Integrals (General)**

    For ANY a, b, c, d ∈ ℝ, the iterated interval integrals commute.
    The integrability hypothesis uses `uIcc` (unordered interval) to
    cover all orderings uniformly.

    This is strictly more general than `intervalIntegral_swap_of_le`:
    no ordering of a ≤ b or c ≤ d is required.

    **Proof strategy**: Reduce to the ordered case via the sign convention
    of interval integrals. The key identities are:
    - `intervalIntegral.integral_symm`: ∫ x in a..b = -∫ x in b..a
    - `intervalIntegral.integral_neg`: ∫ x in a..b, -f x = -∫ x in a..b, f x

    **Why this could be a Mathlib lemma**: This is the natural generalization
    of `integral_integral_swap` to the interval integral API. Currently (as of
    mathlib4 rev 2df2f015) no such standalone lemma exists.
-/
theorem intervalIntegral_swap {f : ℝ → ℝ → ℝ}
    (a b c d : ℝ)
    (hf_meas : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hf_int : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict (uIcc a b)).prod (volume.restrict (uIcc c d)))) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  rcases le_or_lt a b with hab | hab
  · rcases le_or_lt c d with hcd | hcd
    · -- Case 1: a ≤ b, c ≤ d — direct from ordered version
      exact intervalIntegral_swap_of_le a b c d hab hcd hf_meas
        (by rwa [uIcc_of_le hab, uIcc_of_le hcd] at hf_int)
    · -- Case 2: a ≤ b, d < c — flip outer integral sign
      -- Strategy: ∫ y in c..d = -∫ y in d..c, then use ordered swap, then flip back
      have hdc : d ≤ c := le_of_lt hcd
      have hf_int' : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
          ((volume.restrict (Icc a b)).prod (volume.restrict (Icc d c))) := by
        rwa [uIcc_of_le hab, uIcc_of_le hdc, uIcc_comm c d] at hf_int
      -- ∫ y in c..d, (∫ x in a..b, f x y) = -∫ y in d..c, (∫ x in a..b, f x y)
      rw [intervalIntegral.integral_symm d c (fun y => ∫ x in a..b, f x y)]
      -- ∫ y in d..c, (∫ x in a..b, f x y) = ∫ x in a..b, (∫ y in d..c, f x y) [ordered]
      rw [intervalIntegral_swap_of_le a b d c hab hdc hf_meas hf_int']
      -- ∫ x in a..b, (∫ y in d..c, f x y) = -(∫ x in a..b, (∫ y in c..d, f x y))
      simp_rw [intervalIntegral.integral_symm d c (fun y => f · y)]
      rw [intervalIntegral.integral_neg]
      ring
  · rcases le_or_lt c d with hcd | hcd
    · -- Case 3: b < a, c ≤ d — flip inner integral sign
      -- Strategy: ∫ x in a..b, g x = -∫ x in b..a, g x for each y
      have hba : b ≤ a := le_of_lt hab
      have hf_int' : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
          ((volume.restrict (Icc b a)).prod (volume.restrict (Icc c d))) := by
        rwa [uIcc_of_le hba, uIcc_comm a b, uIcc_of_le hcd] at hf_int
      -- Rewrite inner integrals: ∫ x in a..b, f x y = -∫ x in b..a, f x y
      simp_rw [intervalIntegral.integral_symm b a (fun x => f x ·)]
      -- ∫ y in c..d, -∫ x in b..a, f x y = -(∫ y in c..d, ∫ x in b..a, f x y)
      rw [show ∫ y in c..d, -(∫ x in b..a, f x y) = -(∫ y in c..d, ∫ x in b..a, f x y) from
            intervalIntegral.integral_neg (fun y => ∫ x in b..a, f x y)]
      -- ∫ y in c..d, ∫ x in b..a, f x y = ∫ x in b..a, ∫ y in c..d, f x y [ordered]
      rw [intervalIntegral_swap_of_le b a c d hba hcd hf_meas hf_int']
      -- ∫ x in b..a, ∫ y in c..d, f x y = -∫ x in a..b, ∫ y in c..d, f x y
      rw [intervalIntegral.integral_symm b a (fun x => ∫ y in c..d, f x y)]
      ring
    · -- Case 4: b < a, d < c — flip both
      have hba : b ≤ a := le_of_lt hab
      have hdc : d ≤ c := le_of_lt hcd
      have hf_int' : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
          ((volume.restrict (Icc b a)).prod (volume.restrict (Icc d c))) := by
        rwa [uIcc_of_le hba, uIcc_comm a b, uIcc_of_le hdc, uIcc_comm c d] at hf_int
      -- Flip inner: ∫ x in a..b = -∫ x in b..a
      simp_rw [intervalIntegral.integral_symm b a (fun x => f x ·)]
      -- Pull out neg from outer
      rw [show ∫ y in c..d, -(∫ x in b..a, f x y) = -(∫ y in c..d, ∫ x in b..a, f x y) from
            intervalIntegral.integral_neg _]
      -- Flip outer: ∫ y in c..d = -∫ y in d..c
      rw [intervalIntegral.integral_symm d c (fun y => ∫ x in b..a, f x y)]
      -- Now: -(-∫ y in d..c, ∫ x in b..a, f x y) = ∫ y in d..c, ∫ x in b..a, f x y
      -- Apply ordered swap
      rw [neg_neg, intervalIntegral_swap_of_le b a d c hba hdc hf_meas hf_int']
      -- Result: ∫ x in b..a, ∫ y in d..c, f x y
      -- Flip inner back: ∫ y in d..c = -∫ y in c..d
      simp_rw [intervalIntegral.integral_symm d c (fun y => f · y)]
      -- Flip outer back: ∫ x in b..a = -∫ x in a..b
      rw [show ∫ x in b..a, -(∫ y in c..d, f x y) = -(∫ x in b..a, ∫ y in c..d, f x y) from
            intervalIntegral.integral_neg _]
      rw [intervalIntegral.integral_symm b a (fun x => ∫ y in c..d, f x y)]
      ring

/-! ### Part III: Continuous Version -/

/-- **Fubini for Continuous Integrands (no measurability/integrability hypotheses)**

    For continuous f, both measurability and integrability on compact rectangles
    are automatic, giving the cleanest possible statement.

    This applies to all C¹ vector fields (standard in Green's theorem context).
-/
theorem intervalIntegral_swap_of_continuous {f : ℝ → ℝ → ℝ}
    (a b c d : ℝ) (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2)) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  apply intervalIntegral_swap a b c d hf.measurable
  have hcpt : IsCompact (uIcc a b ×ˢ uIcc c d) :=
    isCompact_uIcc.prod isCompact_uIcc
  have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (uIcc a b ×ˢ uIcc c d) volume :=
    hf.continuousOn.integrableOn_compact hcpt
  rwa [Measure.restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint

/-! ### Part IV: Application to Green's Theorem -/

/-- The Fubini hypothesis from GreensTheoremOQ01.lean is dischargeable for
    any continuous partial derivative `∂P/∂y`, via the general swap theorem. -/
theorem greens_fubini_for_continuous_dPdy
    (dPdy : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (h : Continuous dPdy) :
    ∫ y in c..d, ∫ x in a..b, dPdy (x, y) =
    ∫ x in a..b, ∫ y in c..d, dPdy (x, y) :=
  intervalIntegral_swap_of_continuous a b c d (by exact h.comp (Continuous.prod_mk continuous_fst continuous_snd))

/-! ### Part V: Mathlib Gap Analysis -/

/-
## Mathlib Gap Analysis

**Search results** (mathlib4 rev 2df2f015):
- `MeasureTheory.integral_integral_swap`: ∫ x ∂μ, ∫ y ∂ν, g x y = ∫ y ∂ν, ∫ x ∂μ, g x y
  ✓ EXISTS (Fubini for Lebesgue integrals, used internally in our proof)
- `intervalIntegral_swap`: NOT FOUND
- `intervalIntegral.integral_fubini`: NOT FOUND
- `intervalIntegral.swap`: NOT FOUND

The `intervalIntegral_swap` lemma requires the Ioc/Icc bridge (via
`intervalIntegral.integral_of_le`) that is not part of Mathlib's Fubini theorem.

**Contribution target**: `Mathlib.MeasureTheory.Integral.IntervalIntegral`

**Suggested signature for Mathlib PR**:
```lean
theorem MeasureTheory.intervalIntegral.swap {f : ℝ → ℝ → ℝ}
    (a b c d : ℝ)
    (hf : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hi : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      (Measure.prod (volume.restrict (uIcc a b)) (volume.restrict (uIcc c d)))) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y
```
-/

/-! ### Summary

| Theorem | Description | Status |
|---------|-------------|--------|
| `intervalIntegral_swap_of_le` | Ordered case (a ≤ b, c ≤ d) | PROVED |
| `intervalIntegral_swap` | General case (any a,b,c,d) | PROVED |
| `intervalIntegral_swap_of_continuous` | Continuous f, no other hyps | PROVED |
| `greens_fubini_for_continuous_dPdy` | Application to Green's theorem | PROVED |

**Mathlib Gap**: No standalone `intervalIntegral_swap` exists (as of mathlib4 rev 2df2f015).
**Contribution path**: Add to `Mathlib.MeasureTheory.Integral.IntervalIntegral`.

Sorries: 0
Axioms: 0
-/

end GreensTheoremOQ01OQ01OQ02
