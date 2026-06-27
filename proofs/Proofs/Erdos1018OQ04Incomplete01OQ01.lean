/-
# Erdős Problem #1018 OQ-04 (Incomplete-01) — Follow-up OQ-01
## Line Segment Intersection via Convex Hulls

The parent file `Erdos1018OQ04Incomplete01.lean` gives a concrete definition of
topological embeddability of a hypergraph: an injective vertex map `φ` is an
embedding when, for distinct edges `e₁ ≠ e₂`,

    convexHull ℝ (φ '' e₁) ∩ convexHull ℝ (φ '' e₂) ⊆ convexHull ℝ (φ '' (e₁ ∩ e₂)).

This file isolates and proves the geometric core of the `r = 2` (graph) case:
the intersection behaviour of two line segments that share an endpoint.

## What This Provides

1. `convexHull_image_inter_subset` — the *easy* containment that always holds
   (the hull of a shared face is contained in the intersection of the hulls).
   This is one half of the embeddability condition, true for every map `φ`.

2. `segment_inter_segment_of_linearIndependent` — the *substantive* reverse
   direction for two segments `[a,b]` and `[a,c]` sharing the endpoint `a`:
   when the edge vectors `b - a` and `c - a` are linearly independent, the two
   segments meet in *exactly* `{a}`. This is the van Kampen / general-position
   condition that makes the graph case (`r = 2`) of the embeddability definition
   discharge for the shared-vertex pair.

3. `convexHull_pair_inter_of_linearIndependent` — the same statement phrased
   through `convexHull` of the vertex pairs, matching the form used in the
   parent embeddability definition.

The complementary case of two segments with *disjoint* endpoints (which may
still cross) genuinely requires general-position hypotheses and is the open
content; it is documented but not proved here.

## References

- van Kampen, E. (1933). "Komplexe in euklidischen Räumen."
- Matoušek, J. (2003). "Using the Borsuk–Ulam Theorem", §5 (planar embeddings).
-/

import Mathlib.Tactic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment

namespace Erdos1018OQ04Incomplete01OQ01

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ## Part I: The easy containment (holds for every map)

For any vertex map `φ` and any two index sets `s, t`, the convex hull of the
image of `s ∩ t` is contained in the intersection of the two hulls. This is the
"trivial" half of the embeddability condition — it never needs general position.
-/

/-- The hull of the shared face is contained in the intersection of the hulls.
This direction holds unconditionally. -/
theorem convexHull_image_inter_subset {ι : Type*} (φ : ι → E) (s t : Set ι) :
    convexHull ℝ (φ '' (s ∩ t)) ⊆ convexHull ℝ (φ '' s) ∩ convexHull ℝ (φ '' t) := by
  refine subset_inter ?_ ?_
  · exact convexHull_mono (Set.image_subset φ Set.inter_subset_left)
  · exact convexHull_mono (Set.image_subset φ Set.inter_subset_right)

/-! ## Part II: The substantive reverse direction for a shared endpoint

Two segments emanating from a common point `a` meet only at `a`, provided the
two edge directions `b - a` and `c - a` are linearly independent. This is the
general-position condition underlying van Kampen embeddability for graphs.
-/

/-- **Shared-endpoint segment intersection.** If the edge vectors `b - a` and
`c - a` are linearly independent, then the segments `[a, b]` and `[a, c]` meet
in exactly the common endpoint `a`. -/
theorem segment_inter_segment_of_linearIndependent
    {a b c : E} (h : LinearIndependent ℝ ![b - a, c - a]) :
    segment ℝ a b ∩ segment ℝ a c = {a} := by
  refine Set.eq_singleton_iff_unique_mem.2
    ⟨⟨left_mem_segment ℝ a b, left_mem_segment ℝ a c⟩, ?_⟩
  rintro x ⟨hxb, hxc⟩
  rw [segment_eq_image'] at hxb hxc
  obtain ⟨t, _ht, hxt⟩ := hxb
  obtain ⟨s, _hs, hxs⟩ := hxc
  -- `hxt : a + t • (b - a) = x`,  `hxs : a + s • (c - a) = x`
  have h2 : t • (b - a) = s • (c - a) := add_left_cancel (hxt.trans hxs.symm)
  have heq : t • (b - a) + (-s) • (c - a) = 0 := by
    rw [neg_smul, h2]; abel
  obtain ⟨ht0, _⟩ := (LinearIndependent.pair_iff.mp h) t (-s) heq
  rw [← hxt, ht0, zero_smul, add_zero]

/-! ## Part III: Convex-hull phrasing matching the embeddability definition

Re-expressed via `convexHull` of the vertex pairs, this is precisely the
intersection condition appearing in the parent file's `isEmbeddableConc`
specialised to the two graph edges `{a, b}` and `{a, c}`.
-/

/-- The same statement in `convexHull` form: the convex hulls of the vertex
pairs `{a, b}` and `{a, c}` intersect in exactly `{a}` when the edge vectors are
linearly independent. -/
theorem convexHull_pair_inter_of_linearIndependent
    {a b c : E} (h : LinearIndependent ℝ ![b - a, c - a]) :
    convexHull ℝ ({a, b} : Set E) ∩ convexHull ℝ ({a, c} : Set E) = {a} := by
  rw [convexHull_pair, convexHull_pair]
  exact segment_inter_segment_of_linearIndependent h

/-! ## Part IV: Sanity specialisation

A concrete witness that the hypothesis is satisfiable: in `ℝ²` the standard
basis vectors are linearly independent, so the two unit segments from the
origin meet only at the origin. -/

example : segment ℝ (0 : Fin 2 → ℝ) ![1, 0] ∩ segment ℝ (0 : Fin 2 → ℝ) ![0, 1]
    = {(0 : Fin 2 → ℝ)} := by
  apply segment_inter_segment_of_linearIndependent
  rw [LinearIndependent.pair_iff]
  intro s t hst
  -- `s • (![1,0] - 0) + t • (![0,1] - 0) = 0` forces `s = t = 0`
  simp only [sub_zero] at hst
  constructor
  · have := congrFun hst 0; simpa using this
  · have := congrFun hst 1; simpa using this

end Erdos1018OQ04Incomplete01OQ01
