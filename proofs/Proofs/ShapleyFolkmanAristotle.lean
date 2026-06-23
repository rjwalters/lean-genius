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
import Mathlib

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
  rcases Nat.lt_succ_iff_lt_or_eq.mp h with h0 | h1
  · -- card = 0: t is empty, convexHull ∅ = ∅
    have : t = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [this] at hx_hull
    simp [_root_.convexHull_empty] at hx_hull
  · -- card = 1: t = {a}, convexHull {a} = {a}, so x = a ∈ t
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (by omega : t.card = 1)
    rw [Finset.coe_singleton, _root_.convexHull_singleton] at hx_hull
    exact hx_not (by simp [hx_hull])

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
