/-
  Erdős Problem #501 — Measurable-Hull Reduction
  See: https://erdosproblems.com/501  (and Erdos501Problem.lean for the parent)

  ## What this file contributes

  The parent file `Erdos501Problem.lean` leaves `exists_independent_tuple`
  (the Erdős–Hajnal 1960 finite-independence statement) as a `sorry`, together
  with a documented caution: the naive "product outer-measure ≤ integral of
  section outer measures" step used in every prior sketch is the **false
  direction** for non-measurable families (a Sierpiński set has all sections
  null yet full planar outer measure). The correct proof must first replace each
  set `A x` by a Lebesgue-**measurable hull** `H x ⊇ A x` of the same measure,
  and then run a *measurable* Fubini/Tonelli argument. The genuine remaining
  crux is the **joint measurability** of the assignment `x ↦ H x`.

  This file formalizes that first, axiom-free step honestly and completely
  (0 sorries): it constructs the measurable hulls and proves the **reduction**
  that solving the finite/infinite independent-set problem for a family of
  *measurable* sets of measure `< 1` solves it for the original *outer-measure*
  family. This does not resolve the open problem — it isolates the crux exactly.

  Every result below is a genuine `theorem`/`lemma` with a real proof; there are
  no axioms beyond Lean/Mathlib's standard `propext`/`Quot.sound`/`Classical.choice`.
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Tactic

namespace Erdos501Hull

open Set MeasureTheory
open scoped ENNReal

/-- A family of subsets of `ℝ` indexed by reals (mirrors `Erdos501.SetFamily`). -/
def SetFamily := ℝ → Set ℝ

/-- The Lebesgue outer measure of a set. Applying the Lebesgue `Measure`
    (`volume`) to an arbitrary, possibly non-measurable set yields its outer
    measure, so this is literally `volume A`. -/
noncomputable def outerMeasure (A : Set ℝ) : ℝ≥0∞ :=
  volume A

/-- A set `X` is independent for the family `A` if `x ∉ A y` for all distinct
    `x, y ∈ X` (mirrors `Erdos501.IsIndependent`). -/
def IsIndependent (A : SetFamily) (X : Set ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → x ∉ A y

/- ## Part I: Measurable hulls of a single set -/

/-- **Measurable hull.** Every set `A ⊆ ℝ` has a Lebesgue-measurable superset
    `H ⊇ A` with the same measure — namely its outer measure. This is the first
    step of the correct Erdős–Hajnal proof. -/
theorem exists_measurable_hull (A : Set ℝ) :
    ∃ H : Set ℝ, A ⊆ H ∧ MeasurableSet H ∧ volume H = outerMeasure A := by
  obtain ⟨H, hsub, hmeas, hvol⟩ := MeasureTheory.exists_measurable_superset volume A
  exact ⟨H, hsub, hmeas, hvol⟩

/-- A measurable hull of a set of outer measure `< 1` again has measure `< 1`.
    Passing to the hull therefore preserves the bounding hypothesis. -/
theorem exists_measurable_hull_lt_one {A : Set ℝ} (hA : outerMeasure A < 1) :
    ∃ H : Set ℝ, A ⊆ H ∧ MeasurableSet H ∧ volume H < 1 := by
  obtain ⟨H, hsub, hmeas, hvol⟩ := exists_measurable_hull A
  exact ⟨H, hsub, hmeas, hvol ▸ hA⟩

/-- Avoiding the hull implies avoiding the original set: if `A ⊆ H` and
    `x ∉ H`, then `x ∉ A`. This is what makes independence transfer downward
    from the hull family to the original family. -/
theorem notMem_of_notMem_hull {A H : Set ℝ} (hsub : A ⊆ H) {x : ℝ} (hx : x ∉ H) :
    x ∉ A :=
  fun hxA => hx (hsub hxA)

/- ## Part II: Measurable hulls of a whole family -/

/-- **Family-level hull.** For a bounded outer-measure family (each `A x` has
    outer measure `< 1`), there is a family `H` of measurable sets, each of
    measure `< 1`, with `A x ⊆ H x` for every `x`. Uses `choose` (dependent
    choice) to select a hull uniformly in the index. -/
theorem exists_hull_family (A : SetFamily) (hA : ∀ x, outerMeasure (A x) < 1) :
    ∃ H : SetFamily,
      (∀ x, A x ⊆ H x) ∧ (∀ x, MeasurableSet (H x)) ∧ (∀ x, volume (H x) < 1) := by
  choose H hsub hmeas hvol using fun x => exists_measurable_hull_lt_one (hA x)
  exact ⟨H, hsub, hmeas, hvol⟩

/-- **Independence transfer.** If `A x ⊆ H x` pointwise and `X` is independent
    for the hull family `H`, then `X` is independent for the original family
    `A`. (Fewer forbidden points can only make independence easier.) -/
theorem independent_of_hull_independent {A H : SetFamily}
    (hsub : ∀ x, A x ⊆ H x) {X : Set ℝ} (hX : IsIndependent H X) :
    IsIndependent A X := by
  intro x hx y hy hxy hxAy
  exact hX x hx y hy hxy (hsub y hxAy)

/- ## Part III: The reduction -/

/-- **Measurable-hull reduction for Erdős #501.**

    Given any bounded outer-measure family `A` (each `A x` has outer measure
    `< 1`), there is a family `H` of Lebesgue-**measurable** sets, each of
    measure `< 1`, such that *every* set that is independent for `H` is also
    independent for `A`.

    Consequently, to produce independent sets (of any given size, or infinite)
    for the original outer-measure family it suffices to produce them for a
    family of measurable sets of measure `< 1`. This is exactly the reduction
    that makes the Sierpiński-style outer-measure counterexamples irrelevant to
    the *finite* Erdős–Hajnal statement — the remaining obstruction is the
    **joint measurability** of `x ↦ H x`, needed to run measurable Fubini. -/
theorem outerMeasure_problem_reduces_to_measurable
    (A : SetFamily) (hA : ∀ x, outerMeasure (A x) < 1) :
    ∃ H : SetFamily,
      (∀ x, MeasurableSet (H x)) ∧ (∀ x, volume (H x) < 1) ∧
      (∀ X : Set ℝ, IsIndependent H X → IsIndependent A X) := by
  obtain ⟨H, hsub, hmeas, hvol⟩ := exists_hull_family A hA
  exact ⟨H, hmeas, hvol, fun _X hX => independent_of_hull_independent hsub hX⟩

/-- Specialisation of the reduction to *finite* independent sets of a fixed
    size `n`: a size-`n` independent set for the measurable hull family yields a
    size-`n` independent set (indeed the very same one) for `A`. -/
theorem independentFinset_of_hull {A H : SetFamily}
    (hsub : ∀ x, A x ⊆ H x) {X : Finset ℝ} {n : ℕ}
    (hcard : X.card = n) (hX : IsIndependent H ↑X) :
    ∃ Y : Finset ℝ, Y.card = n ∧ IsIndependent A ↑Y :=
  ⟨X, hcard, independent_of_hull_independent hsub hX⟩

end Erdos501Hull
