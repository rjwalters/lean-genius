import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Counting triangles that cover an independent set

Distinct independent vertices require distinct covering triangles. If a
known triangle family avoids those vertices, its triangles can be counted
in addition. This is a graph counting lemma, with no C4 or spectrum premise.
-/

namespace Erdos85
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A known family of triangles avoiding an independent set can be added
to one distinct covering triangle for each vertex of that set. -/
theorem independent_triangle_cover_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (known : Finset (Finset V))
    (hind : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v)
    (hcover : ∀ v ∈ S, ∃ t ∈ G.cliqueFinset 3, v ∈ t)
    (hknown : known ⊆ G.cliqueFinset 3)
    (havoid : ∀ t ∈ known, Disjoint S t) :
    known.card + S.card ≤ (G.cliqueFinset 3).card := by
  classical
  have hchoose : ∀ v : S, ∃ t ∈ G.cliqueFinset 3, v.val ∈ t := by
    intro v
    exact hcover v.val v.property
  choose f hf hmem using hchoose
  have hinj : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    by_contra hne
    have hv : v.val ∈ f u := by rw [huv]; exact hmem v
    have hclique := (G.mem_cliqueFinset_iff.mp (hf u)).isClique
    exact hind u.val u.property v.val v.property hne
      (hclique (hmem u) hv hne)
  let chosen := Finset.univ.image f
  have hcard : chosen.card = S.card := by
    dsimp [chosen]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hdis : Disjoint known chosen := by
    apply Finset.disjoint_left.mpr
    intro t htk htc
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp htc
    exact Finset.disjoint_left.mp (havoid (f v) htk) v.property (hmem v)
  have hsub : known ∪ chosen ⊆ G.cliqueFinset 3 := by
    intro t ht
    rcases Finset.mem_union.mp ht with hk | hc
    · exact hknown hk
    · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hc
      exact hf v
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, hcard] at hle
  exact hle

/-- Without independence, each additional triangle can cover at most
three vertices outside the known family. -/
theorem triangle_cover_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (known : Finset (Finset V))
    (hcover : ∀ v ∈ S, ∃ t ∈ G.cliqueFinset 3, v ∈ t)
    (hknown : known ⊆ G.cliqueFinset 3)
    (havoid : ∀ t ∈ known, Disjoint S t) :
    S.card ≤ 3 * ((G.cliqueFinset 3).card - known.card) := by
  classical
  let rest := G.cliqueFinset 3 \ known
  have hsub : S ⊆ rest.biUnion id := by
    intro v hv
    obtain ⟨t, ht, hvt⟩ := hcover v hv
    have hnot : t ∉ known := by
      intro hk
      exact Finset.disjoint_left.mp (havoid t hk) hv hvt
    exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_sdiff.mpr ⟨ht, hnot⟩, hvt⟩
  have hsum : (∑ t ∈ rest, t.card) = 3 * rest.card := by
    calc
      _ = ∑ _t ∈ rest, 3 := Finset.sum_congr rfl (by
        intro t ht
        exact (G.mem_cliqueFinset_iff.mp (Finset.mem_sdiff.mp ht).1).card_eq)
      _ = _ := by simp [Nat.mul_comm]
  have hcard : rest.card = (G.cliqueFinset 3).card - known.card :=
    Finset.card_sdiff_of_subset hknown
  calc
    S.card ≤ (rest.biUnion id).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ rest, t.card := Finset.card_biUnion_le
    _ = 3 * ((G.cliqueFinset 3).card - known.card) := by rw [hsum, hcard]

/-- Three independent triangle-covered vertices disjoint from a known
triangle force at least four triangles. -/
theorem four_triangles_of_independent_three_and_disjoint_triangle
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S t : Finset V) (hcard : S.card = 3)
    (hind : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v)
    (hcover : ∀ v ∈ S, ∃ s ∈ G.cliqueFinset 3, v ∈ s)
    (htriangle : G.IsNClique 3 t) (havoid : Disjoint S t) :
    4 ≤ (G.cliqueFinset 3).card := by
  have hknown : ({t} : Finset (Finset V)) ⊆ G.cliqueFinset 3 := by
    simpa using G.mem_cliqueFinset_iff.mpr htriangle
  have h := independent_triangle_cover_bound G S {t} hind hcover hknown (by
    intro s hs
    have heq := Finset.mem_singleton.mp hs
    subst s
    exact havoid)
  simpa [hcard] using h

end Erdos85

#print axioms Erdos85.independent_triangle_cover_bound
#print axioms Erdos85.triangle_cover_card_bound
#print axioms Erdos85.four_triangles_of_independent_three_and_disjoint_triangle
