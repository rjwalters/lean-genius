/-
  Aristotle targets for Shapley-Folkman Lemma
  Routine supporting lemmas for automated proof search.
  See ShapleyFolkman.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main Shapley-Folkman theorem
  - Known result likely provable from Mathlib
  - Clean theorem statement with no definition sorries
  - No axioms
-/
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Finset.Pointwise

set_option linter.unusedVariables false

open Set Finset Pointwise

namespace ShapleyFolkmanAristotle

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A single point is in the convex hull of any set containing it. -/
theorem singleton_mem_convexHull {s : Set E} {x : E} (hx : x ∈ s) :
    x ∈ convexHull ℝ s :=
  subset_convexHull ℝ s hx

/-- The convex hull of a singleton is just the singleton. -/
theorem convexHull_singleton (x : E) :
    convexHull ℝ ({x} : Set E) = {x} :=
  _root_.convexHull_singleton x

/-- If x is in the convex hull of a nonempty finset and x is not in the finset,
    then the finset has at least 2 elements. -/
theorem card_ge_two_of_mem_convexHull_not_mem {t : Finset E} {x : E}
    (hx_hull : x ∈ convexHull ℝ (↑t : Set E))
    (hx_not : x ∉ (↑t : Set E)) :
    2 ≤ t.card := by
  by_contra h
  push_neg at h
  have hle : t.card ≤ 1 := by omega
  rcases t.eq_empty_or_nonempty with hempty | ⟨a, ha⟩
  · -- t = ∅: convexHull ℝ ∅ = ∅, contradicts x ∈ convexHull ℝ ↑t
    rw [hempty, Finset.coe_empty, _root_.convexHull_empty] at hx_hull
    exact Set.not_mem_empty x hx_hull
  · -- t has card ≤ 1 with a ∈ t, so t = {a}
    have hsing : t = {a} := by
      ext b; constructor
      · exact fun hb => Finset.mem_singleton.mpr
          (Finset.card_le_one.mp hle hb ha)
      · exact fun hb => (Finset.mem_singleton.mp hb) ▸ ha
    rw [hsing, Finset.coe_singleton, _root_.convexHull_singleton] at hx_hull
    rw [hsing, Finset.coe_singleton] at hx_not
    exact hx_not (Set.mem_singleton_iff.mpr hx_hull ▸ Set.mem_singleton a)

/-- In a FiniteDimensional space, more than finrank+1 points cannot be
    affinely independent. -/
theorem not_affineIndependent_of_card_gt [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E + 1 < n)
    {f : Fin n → E} :
    ¬AffineIndependent ℝ f := by
  intro haf
  have hcard := haf.fintype_card_le_finrank_succ
  simp [Fintype.card_fin] at hcard
  omega

/-- The convex hull of the empty set is empty. -/
theorem convexHull_empty :
    convexHull ℝ (∅ : Set E) = ∅ :=
  _root_.convexHull_empty

/-- If a point lies in a convex set, it lies in the convex hull of that set. -/
theorem mem_convexHull_of_mem_convex {s : Set E} (hs : Convex ℝ s) {x : E}
    (hx : x ∈ s) : x ∈ convexHull ℝ s :=
  subset_convexHull ℝ s hx

/-- The Minkowski sum of convex hulls is convex. -/
theorem convex_sum_convexHull {s₁ s₂ : Set E} :
    Convex ℝ (convexHull ℝ s₁ + convexHull ℝ s₂) :=
  (convex_convexHull ℝ s₁).add (convex_convexHull ℝ s₂)

/-- A point that equals exactly one element of a set is in that set. -/
theorem mem_of_sum_singleton {s : Set E} {x : E} {a : E}
    (ha : a ∈ s) (hx : x = 1 • a) : x ∈ s := by
  rw [hx, one_smul]; exact ha

end ShapleyFolkmanAristotle
