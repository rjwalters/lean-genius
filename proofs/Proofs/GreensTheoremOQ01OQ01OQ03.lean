/-
  Weakened Integrability for Interval Integral Swap (greens-theorem-oq-01-oq-01-oq-03)

  Open Question from greens-theorem-oq-01-oq-01:
  "The integrability hypothesis uses the product of Icc-restricted measures.
  Can this be weakened to just L¹ integrability on the open rectangle
  Ioo a b × Ioo c d, and does Mathlib provide the necessary tools?"

  ## Answer: YES.

  For the Lebesgue measure on ℝ, vol.restrict (Icc a b) = vol.restrict (Ioo a b)
  because the boundary {a, b} has Lebesgue measure zero (singletons are countable).
  Therefore:
    Integrable f (vol.restrict Icc × vol.restrict Icc) ↔
    Integrable f (vol.restrict Ioo × vol.restrict Ioo)

  The integrability hypothesis can be weakened to the open rectangle without
  changing the theorem. The proof proceeds in three steps:

  1. vol (Icc a b \ Ioo a b) = 0  (boundary has measure zero)
  2. vol.restrict (Icc a b) = vol.restrict (Ioo a b)  (measures agree)
  3. Apply existing Fubini theorem after converting Ioo → Icc integrability

  ## Mathlib Tools

  - Set.Countable.measure_zero: countable sets have measure zero
  - measure_mono_null: subsets of null sets are null
  - measure_union_null: union of null sets is null
  - measure_union_le: subadditivity of measure
  - Measure.ext: extensionality for measures
  - MeasureTheory.integral_integral_swap: Fubini for Lebesgue integrals

  ## Status: 0 sorries, 0 axioms
-/
import Mathlib

open MeasureTheory intervalIntegral Set Measure Filter Topology

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace GreensTheoremOQ01OQ01OQ03

/-! ### Part I: Null Boundary Lemmas -/

/-- The left boundary point of [a,b] has Lebesgue measure zero. -/
private lemma volume_singleton_zero (a : ℝ) : volume ({a} : Set ℝ) = 0 :=
  (Set.countable_singleton a).measure_zero volume

/-- The closed-open difference Icc a b \ Ioo a b is contained in {a, b},
    so it has Lebesgue measure zero. -/
lemma volume_Icc_sdiff_Ioo (a b : ℝ) :
    MeasureTheory.volume (Set.Icc a b \ Set.Ioo a b) = 0 :=
  measure_mono_null
    (fun x hx => by
      rw [Set.mem_diff, Set.mem_Icc, Set.mem_Ioo] at hx
      simp only [Set.mem_union, Set.mem_singleton_iff]
      obtain ⟨⟨ha, hb⟩, hlt⟩ := hx
      push_neg at hlt
      -- hlt : a < x → b ≤ x; combined with ha : a ≤ x and hb : x ≤ b
      rcases lt_or_eq_of_le ha with ha' | ha'
      · right; exact le_antisymm hb (hlt ha')
      · left; exact ha'.symm)
    (measure_union_null (volume_singleton_zero a) (volume_singleton_zero b))

/-! ### Part II: Restriction Equality -/

/-- For Lebesgue measure on ℝ, the restriction to a closed interval equals the
    restriction to the corresponding open interval. The boundary has measure zero,
    so no mass is lost or gained when switching between Icc and Ioo. -/
theorem volume_restrict_Icc_eq_Ioo (a b : ℝ) :
    MeasureTheory.volume.restrict (Set.Icc a b) =
    MeasureTheory.volume.restrict (Set.Ioo a b) := by
  ext s hs
  simp only [Measure.restrict_apply hs]
  apply le_antisymm
  · -- volume (s ∩ Icc a b) ≤ volume (s ∩ Ioo a b)
    -- Because s ∩ Icc ⊆ (s ∩ Ioo) ∪ (Icc \ Ioo), and (Icc \ Ioo) is null
    have h1 : s ∩ Set.Icc a b ⊆ s ∩ Set.Ioo a b ∪ (Set.Icc a b \ Set.Ioo a b) := by
      intro x ⟨hxs, hxIcc⟩
      by_cases hx' : x ∈ Set.Ioo a b
      · exact Or.inl ⟨hxs, hx'⟩
      · exact Or.inr ⟨hxIcc, hx'⟩
    calc MeasureTheory.volume (s ∩ Set.Icc a b)
        ≤ MeasureTheory.volume (s ∩ Set.Ioo a b ∪ (Set.Icc a b \ Set.Ioo a b)) :=
            measure_mono h1
      _ ≤ MeasureTheory.volume (s ∩ Set.Ioo a b) +
          MeasureTheory.volume (Set.Icc a b \ Set.Ioo a b) :=
            measure_union_le _ _
      _ = MeasureTheory.volume (s ∩ Set.Ioo a b) := by
            rw [volume_Icc_sdiff_Ioo, add_zero]
  · -- volume (s ∩ Ioo a b) ≤ volume (s ∩ Icc a b)  (Ioo ⊆ Icc)
    exact measure_mono (Set.inter_subset_inter_right s Set.Ioo_subset_Icc_self)

/-- The product of Icc-restricted measures equals the product of Ioo-restricted
    measures, for all pairs of endpoints. -/
theorem volume_prod_restrict_Icc_eq_Ioo (a b c d : ℝ) :
    (MeasureTheory.volume.restrict (Set.Icc a b)).prod
      (MeasureTheory.volume.restrict (Set.Icc c d)) =
    (MeasureTheory.volume.restrict (Set.Ioo a b)).prod
      (MeasureTheory.volume.restrict (Set.Ioo c d)) := by
  rw [volume_restrict_Icc_eq_Ioo a b, volume_restrict_Icc_eq_Ioo c d]

/-! ### Part III: Core Fubini Step (inline from OQ-01-OQ-01) -/

/-- The core Fubini step for ordered intervals with Icc integrability.
    Converts interval integrals to set integrals and applies Mathlib's
    abstract Fubini theorem for Lebesgue integrals. -/
private theorem fubini_core {f : ℝ → ℝ → ℝ}
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hf_meas : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hf_int : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
       (MeasureTheory.volume.restrict (Set.Icc c d)))) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  rw [intervalIntegral.integral_of_le hcd]
  conv_rhs => rw [intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  have hf_int' : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
       (MeasureTheory.volume.restrict (Set.Ioc c d))) :=
    hf_int.mono_measure (Measure.prod_mono
      (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
      (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl))
  exact (MeasureTheory.integral_integral_swap hf_int').symm

/-! ### Part IV: Main Theorems -/

/-- **Fubini for Interval Integrals with Open Rectangle Integrability (Ordered)**

    The integrability hypothesis can be weakened from the closed rectangle
    [a,b] × [c,d] to the open rectangle (a,b) × (c,d).

    For Lebesgue measure, these are equivalent: vol.restrict Icc = vol.restrict Ioo
    since the boundary {a,b} and {c,d} have measure zero.

    This answers the open question from greens-theorem-oq-01-oq-01:
    "YES — the Icc integrability hypothesis is equivalent to Ioo integrability." -/
theorem intervalIntegral_swap_of_Ioo_integrable {f : ℝ → ℝ → ℝ}
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hf_meas : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hf_int : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
      ((MeasureTheory.volume.restrict (Set.Ioo a b)).prod
       (MeasureTheory.volume.restrict (Set.Ioo c d)))) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  apply fubini_core a b c d hab hcd hf_meas
  rw [volume_restrict_Icc_eq_Ioo a b, volume_restrict_Icc_eq_Ioo c d]
  exact hf_int

/-- **Equivalence**: Icc integrability ↔ Ioo integrability for Lebesgue measure.

    This makes the equivalence explicit: the integrability conditions are
    identical for Lebesgue measure. -/
theorem integrable_Icc_iff_Ioo {f : ℝ × ℝ → ℝ} (a b c d : ℝ) :
    Integrable f ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
                   (MeasureTheory.volume.restrict (Set.Icc c d))) ↔
    Integrable f ((MeasureTheory.volume.restrict (Set.Ioo a b)).prod
                   (MeasureTheory.volume.restrict (Set.Ioo c d))) := by
  rw [volume_prod_restrict_Icc_eq_Ioo]

/-! ### Part V: Application to Green's Theorem -/

/-- For Green's theorem: the hFubini hypothesis can use either open or closed
    rectangle integrability. For continuous partial derivatives, both hold
    automatically (compact rectangle ⊆ open rectangle via integrability). -/
theorem greens_fubini_open_rectangle
    (dPdy : ℝ × ℝ → ℝ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hf_meas : Measurable dPdy)
    (hf_int : Integrable dPdy
      ((MeasureTheory.volume.restrict (Set.Ioo a b)).prod
       (MeasureTheory.volume.restrict (Set.Ioo c d)))) :
    ∫ y in c..d, ∫ x in a..b, dPdy (x, y) =
    ∫ x in a..b, ∫ y in c..d, dPdy (x, y) :=
  -- fun p => dPdy (p.1, p.2) and dPdy are definitionally equal
  intervalIntegral_swap_of_Ioo_integrable a b c d hab hcd hf_meas hf_int

/-! ### Part VI: Mathlib Gap Analysis -/

/-
## Mathlib Gap Analysis

**Search results** (mathlib4 current):

The key tools used here are ALL in Mathlib:
- `Set.Countable.measure_zero`: countable sets have measure zero
- `measure_mono_null`: monotonicity of null sets
- `measure_union_null`: union of null sets is null
- `measure_union_le`: subadditivity of measure
- `Measure.restrict_apply`: restriction measure on measurable sets
- `Set.inter_subset_inter_right`: intersection monotonicity
- `Set.Ioo_subset_Icc_self`: Ioo ⊆ Icc

The key THEOREM proved here:
  `volume.restrict (Icc a b) = volume.restrict (Ioo a b)`
This is NOT in Mathlib as a standalone lemma (as of current revision).

**Why this is not in Mathlib**:
  Mathlib tends to work with `Ioc` (half-open intervals) as the canonical
  interval for Lebesgue measure theory (since `Ioc a b` is a π-system for
  standard Borel measure construction). The Icc = Ioo equivalence under
  Lebesgue measure is derivable but not prominently featured.

**Contribution path**:
  `volume_restrict_Icc_eq_Ioo` could be contributed to
  `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` as a @[simp] lemma.
  More generally: for any atomless Borel measure, restricting to any of
  Ioo, Ioc, Ico, Icc gives the same result (boundaries are null).

## Summary

| Theorem | Description | Status |
|---------|-------------|--------|
| `volume_Icc_sdiff_Ioo` | vol(Icc \ Ioo) = 0 | PROVED |
| `volume_restrict_Icc_eq_Ioo` | Restriction equality | PROVED |
| `volume_prod_restrict_Icc_eq_Ioo` | Product measure equality | PROVED |
| `intervalIntegral_swap_of_Ioo_integrable` | Main Fubini with Ioo | PROVED |
| `integrable_Icc_iff_Ioo` | Equivalence of conditions | PROVED |
| `greens_fubini_open_rectangle` | Application to Green's | PROVED |

**Answer to OQ-03**: YES. The Icc integrability hypothesis can be replaced by
Ioo integrability (or any boundary variant: Ioc, Ico) because for Lebesgue
measure these restrictions are identical. Mathlib provides all needed tools.

Sorries: 0
Axioms: 0
-/

end GreensTheoremOQ01OQ01OQ03
