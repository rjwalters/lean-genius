/-
  The rationals are not a Gδ set in ℝ, and no function ℝ → ℝ is continuous
  exactly at the rationals.

  Open question OQ-01-OQ-03 (parent: baire-category-theorem, via OQ-01).

  The Baire-category entry and its descendants exploit the *residual / meagre*
  dichotomy in a complete metric space: a dense Gδ set cannot be meagre
  (`not_isMeagre_of_isGδ_of_dense`), whereas any countable subset of a space
  with no isolated points *is* meagre (a countable union of nowhere-dense
  singletons). Sibling OQ-01-OQ-02 turned this into a cardinality floor
  (𝔠 ≤ #α). This file turns the SAME dichotomy into a *Gδ obstruction* and its
  most famous consequence in real analysis.

  Concretely:

  * `not_isGδ_rationals` : the set `ℚ ⊆ ℝ` (the range of the cast `ℚ → ℝ`) is
    NOT a Gδ set. If it were, being dense it would be residual, hence not
    meagre; but it is meagre, a contradiction.

  * `IsGδ.setOf_continuousAt` (Mathlib) : for any `f : ℝ → ℝ` the set of points
    of continuity `{x | ContinuousAt f x}` is a Gδ.

  Combining the two yields the capstone, classically discussed alongside
  Thomae's function:

      no `f : ℝ → ℝ` is continuous at every rational and discontinuous at every
      irrational — i.e. the set of continuity points can never equal `ℚ`.

  The asymmetry is sharp: the *irrationals* ARE a Gδ (`IsGδ.setOf_irrational`),
  so Thomae's function (continuous exactly at the irrationals) is not obstructed
  — only the rational side is impossible.

  Relation to neighbours.  The entry `algebraic-reals-meager-dense-gdelta`
  records the dual "algebraic reals are not a Gδ" using the same countable-set
  mechanism; that `ℚ` is not a Gδ is the textbook special case. The genuinely
  new content here is the *function-theoretic capstone*: gluing the not-Gδ fact
  to `IsGδ.setOf_continuousAt` to rule out any continuity set equal to `ℚ`.

  Everything is proved from Mathlib; 0 axioms, 0 sorries.
-/
import Mathlib

open Set Topology

namespace BaireRationalsNotGdelta

/-- The rationals, realised as a subset of `ℝ` via the coercion `ℚ → ℝ`. -/
def rationals : Set ℝ := Set.range ((↑) : ℚ → ℝ)

/-- `rationals` is exactly the complement of the irrationals: `Irrational x` is by
definition `x ∉ range ((↑) : ℚ → ℝ)`. -/
theorem rationals_eq_compl_irrational :
    rationals = {x : ℝ | Irrational x}ᶜ := by
  ext x
  simp [rationals, Irrational]

/-- The rationals are dense in `ℝ`. -/
theorem dense_rationals : Dense rationals :=
  Rat.denseRange_cast

/-- A nowhere-dense set is meagre (it is a one-element countable union of
nowhere-dense sets). -/
theorem IsNowhereDense.isMeagre {X : Type*} [TopologicalSpace X] {s : Set X}
    (h : IsNowhereDense s) : IsMeagre s := by
  rw [isMeagre_iff_countable_union_isNowhereDense]
  exact ⟨{s}, by simpa using h, countable_singleton s, by simp⟩

/-- In `ℝ` every singleton is meagre: it is closed with empty interior (`ℝ` has
no isolated points), hence nowhere dense. -/
theorem isMeagre_singleton_real (x : ℝ) : IsMeagre ({x} : Set ℝ) := by
  apply IsNowhereDense.isMeagre
  rw [(isClosed_singleton).isNowhereDense_iff, interior_singleton]

/-- The rationals form a meagre subset of `ℝ`: a countable union of the
nowhere-dense singletons `{q}`. -/
theorem isMeagre_rationals : IsMeagre rationals := by
  have hrange : rationals = ⋃ q : ℚ, {((q : ℝ))} := by
    rw [rationals, ← Set.iUnion_singleton_eq_range]
  rw [hrange]
  exact isMeagre_iUnion (fun q => isMeagre_singleton_real _)

/-- **The rationals are not a Gδ set in `ℝ`.**  A dense Gδ set in a Baire space
is residual, hence not meagre; but `ℚ` is meagre. -/
theorem not_isGδ_rationals : ¬ IsGδ rationals := by
  intro h
  exact not_isMeagre_of_isGδ_of_dense h dense_rationals isMeagre_rationals

/-- Restatement: the set of points where `x` is *not* irrational is not a Gδ. -/
theorem not_isGδ_setOf_not_irrational :
    ¬ IsGδ {x : ℝ | ¬ Irrational x} := by
  have : {x : ℝ | ¬ Irrational x} = rationals := by
    rw [rationals_eq_compl_irrational]; ext x; simp
  rw [this]; exact not_isGδ_rationals

/-- The companion (Mathlib) fact, recorded for contrast: the *irrationals* ARE a
Gδ set.  Thus the Gδ property splits the two sides of `ℝ` asymmetrically. -/
theorem isGδ_irrationals : IsGδ {x : ℝ | Irrational x} :=
  IsGδ.setOf_irrational

/-- **Capstone.**  For every `f : ℝ → ℝ`, the set of continuity points is never
equal to the rationals: no function is continuous at exactly the rational
points.  (The continuity set is always a Gδ, and `ℚ` is not.) -/
theorem continuitySet_ne_rationals (f : ℝ → ℝ) :
    {x : ℝ | ContinuousAt f x} ≠ rationals := by
  intro h
  exact not_isGδ_rationals (h ▸ IsGδ.setOf_continuousAt f)

/-- Capstone, in "no such function" form.  There is no `f : ℝ → ℝ` that is
continuous at every rational and discontinuous at every irrational. -/
theorem no_function_continuous_exactly_at_rationals :
    ¬ ∃ f : ℝ → ℝ, (∀ x, ContinuousAt f x ↔ ¬ Irrational x) := by
  rintro ⟨f, hf⟩
  apply continuitySet_ne_rationals f
  rw [rationals_eq_compl_irrational]
  ext x
  simpa using hf x

/-- The irrational side, by contrast, is *not* obstructed at the Gδ level: the
set of continuity points is allowed to equal the irrationals.  (Existence of an
actual such function — Thomae's function — is a separate construction; here we
record only that no Gδ obstruction rules it out, unlike the rational side.) -/
theorem irrationals_isGδ_no_obstruction :
    IsGδ {x : ℝ | Irrational x} ∧ ¬ IsGδ {x : ℝ | ¬ Irrational x} :=
  ⟨isGδ_irrationals, not_isGδ_setOf_not_irrational⟩

end BaireRationalsNotGdelta
