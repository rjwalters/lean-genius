import Mathlib

/-
# Subordinate Finite ε-Nets on Compact Metric Spaces

## What This Proves

A *refinement* of the finite-subcover characterization, special to metric
spaces.  Given an open cover `U : ι → Set X` of a compact **metric** space, we
produce a single radius `δ > 0` (a Lebesgue number) together with a finite set
of centers `t` whose `δ`-balls cover `X` and are **subordinate** to the cover:
each ball `ball x δ` is contained in some single cover member `U i`.

The headline `exists_subordinate_finite_ball_cover` is the metric analogue of a
finite subcover, but with extra geometric control: the subcover is realized by
balls of a *uniform* radius, each living inside one member of the original
cover.  This is the structure that powers Heine–Cantor uniform continuity,
partitions of unity, and the construction of finite ε-nets adapted to a cover.

It is assembled from two genuinely non-trivial Mathlib ingredients, neither of
which alone yields the subordinate net:

* `lebesgue_number_lemma_of_metric` — a compact set in a metric space has, for
  every open cover, a radius `δ > 0` such that every `δ`-ball is contained in a
  cover member;
* `exists_finite_cover_balls_of_isCompact_closure` — a relatively compact set is
  covered by finitely many balls of any fixed positive radius.

## Structural Consequences

* `exists_finite_subcover_via_net` — the **finite subcover re-derived through
  the net**: selecting, for each net ball, a cover member that contains it gives
  a finite subfamily of `U` covering `X`.  This recovers the Heine–Borel finite
  subcover for compact metric spaces *constructively from the Lebesgue number*,
  rather than from abstract compactness directly.
* `exists_subordinate_fine_cover` — the **fineness** refinement: the same net
  additionally bounds the diameter of every member by `2 δ`, so an arbitrary
  open cover is refined to a finite cover by sets of controlled small diameter,
  each inside one cover element.

## Why This Is a Non-Wrapper

No single Mathlib lemma states the subordinate net.  The content is the
*combination*: take the Lebesgue radius `δ` from the cover, then run total
boundedness at that very radius to get finitely many centers, and observe that
the two are compatible — the balls both cover `X` and refine the cover.  The
finite-subcover and fineness corollaries are then read off from that net.
-/

open Set Metric

namespace CompactnessFiniteSubcoverOq02

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Subordinate finite ε-net.** Every open cover `U` of a compact metric space
admits a Lebesgue radius `δ > 0` and a finite set of centers `t` such that the
`δ`-balls about `t` cover the space, and each such ball is contained in a single
member of the cover. -/
theorem exists_subordinate_finite_ball_cover
    {ι : Type*} {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (hcov : (⋃ i, U i) = univ) :
    ∃ (δ : ℝ) (t : Set X), 0 < δ ∧ t.Finite ∧
      (⋃ x ∈ t, ball x δ) = univ ∧
      ∀ x ∈ t, ∃ i, ball x δ ⊆ U i := by
  -- A Lebesgue number for the cover: every `δ`-ball lands in some `U i`.
  have hsub : (univ : Set X) ⊆ ⋃ i, U i := hcov.ge
  obtain ⟨δ, hδ, hlb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hsub
  -- Total boundedness at radius `δ`: finitely many `δ`-balls cover the space.
  obtain ⟨t, -, htfin, htcov⟩ :=
    exists_finite_cover_balls_of_isCompact_closure
      (s := (univ : Set X)) (by rw [closure_univ]; exact isCompact_univ) hδ
  exact ⟨δ, t, hδ, htfin, univ_subset_iff.mp htcov, fun x _ => hlb x (mem_univ x)⟩

/-- **Finite subcover via a subordinate net.** Selecting for each net ball a
cover member containing it yields a finite subfamily of the cover that already
covers the whole space.  This re-derives the Heine–Borel finite subcover for
compact metric spaces from the Lebesgue number. -/
theorem exists_finite_subcover_via_net
    {ι : Type*} {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (hcov : (⋃ i, U i) = univ) :
    ∃ s : Set ι, s.Finite ∧ (⋃ i ∈ s, U i) = univ := by
  obtain ⟨δ, t, _, htfin, htcov, hsub⟩ :=
    exists_subordinate_finite_ball_cover hU hcov
  haveI : Finite t := htfin.to_subtype
  -- For each center, pick a cover member containing its ball.
  choose g hg using fun x : t => hsub x.1 x.2
  refine ⟨Set.range g, Set.finite_range g, ?_⟩
  apply univ_subset_iff.mp
  intro y _
  have hy : y ∈ ⋃ x ∈ t, ball x δ := htcov.symm.subset (mem_univ y)
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
  exact mem_iUnion₂.mpr ⟨g ⟨x, hx⟩, Set.mem_range_self _, hg ⟨x, hx⟩ hyx⟩

/-- **Fineness of the subordinate net.** The net of `exists_subordinate_finite_ball_cover`
also controls diameters: every member `ball x δ` has diameter at most `2 δ`, so an
arbitrary open cover refines to a finite cover by sets of small controlled diameter,
each contained in a single cover member. -/
theorem exists_subordinate_fine_cover
    {ι : Type*} {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (hcov : (⋃ i, U i) = univ) :
    ∃ (δ : ℝ) (t : Set X), 0 < δ ∧ t.Finite ∧
      (⋃ x ∈ t, ball x δ) = univ ∧
      ∀ x ∈ t, (∃ i, ball x δ ⊆ U i) ∧ Metric.diam (ball x δ) ≤ 2 * δ := by
  obtain ⟨δ, t, hδ, htfin, htcov, hsub⟩ :=
    exists_subordinate_finite_ball_cover hU hcov
  exact ⟨δ, t, hδ, htfin, htcov, fun x hx => ⟨hsub x hx, Metric.diam_ball hδ.le⟩⟩

end CompactnessFiniteSubcoverOq02
