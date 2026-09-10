import Proofs.Erdos85OrderFortyNineEmptyTriangleCover
import Proofs.Erdos85WitnessedTriangleMatchingCover

/-! Actual triangle-cover bound using only edges with exterior common neighbors. -/
namespace Erdos85
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

/-- After accounting for every triangle inside E, the remaining cover can
save triangles only through disjoint edges with common neighbors outside E. -/
theorem orderFortyNine_empty_exterior_matching_triangle_cover_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (E S : Finset (↑(orderFortyNineLowVertices G) : Set V))
    (known : Finset (Finset (↑(orderFortyNineLowVertices G) : Set V)))
    (ν : ℕ)
    (hSE : S ⊆ E)
    (hempty : ∀ x ∈ S,
      (G.neighborFinset x.val ∩ orderFortyNineHighVertices G).card = 0)
    (hknown : known ⊆ (G.induce (↑(orderFortyNineLowVertices G) : Set V)).cliqueFinset 3)
    (havoid : ∀ t ∈ known, Disjoint S t)
    (hinside : ∀ t ∈ (G.induce (↑(orderFortyNineLowVertices G) : Set V)).cliqueFinset 3,
      t ⊆ E → t ∈ known)
    (hmatching : ∀ P : Finset (Finset (↑(orderFortyNineLowVertices G) : Set V)),
      (∀ e ∈ P,
        (G.induce (↑(orderFortyNineLowVertices G) : Set V)).IsNClique 2 e ∧ e ⊆ S ∧
        ∃ z ∉ E, ∀ v ∈ e, G.Adj v.val z.val) →
      (∀ e ∈ P, ∀ d ∈ P, e ≠ d → Disjoint e d) → P.card ≤ ν) :
    known.card + S.card ≤
      ((G.induce (↑(orderFortyNineLowVertices G) : Set V)).cliqueFinset 3).card + ν := by
  classical
  let L := G.induce (↑(orderFortyNineLowVertices G) : Set V)
  let rest := L.cliqueFinset 3 \ known
  have hcover : ∀ x ∈ S, ∃ t ∈ rest, x ∈ t := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := orderFortyNine_empty_low_vertex_mem_triangle
      G hfree hmin hcard x (hempty x hx)
    refine ⟨t, Finset.mem_sdiff.mpr ⟨ht, ?_⟩, hxt⟩
    intro hk
    exact Finset.disjoint_left.mp (havoid t hk) hx hxt
  obtain ⟨P, hP, hdis, hcount⟩ :=
    triangle_cover_extract_exterior_disjoint_pairs L E S rest hSE
      Finset.sdiff_subset hcover (by
        intro t ht hsub
        exact (Finset.mem_sdiff.mp ht).2 (hinside t (Finset.mem_sdiff.mp ht).1 hsub))
  have hbound : P.card ≤ ν := hmatching P hP hdis
  have h : S.card ≤ rest.card + ν := hcount.trans (Nat.add_le_add_left hbound _)
  have hrest : rest.card = (L.cliqueFinset 3).card - known.card :=
    Finset.card_sdiff_of_subset hknown
  have hle : known.card ≤ (L.cliqueFinset 3).card := Finset.card_le_card hknown
  change known.card + S.card ≤ (L.cliqueFinset 3).card + ν
  rw [hrest] at h
  omega

end
end Erdos85
#print axioms Erdos85.orderFortyNine_empty_exterior_matching_triangle_cover_bound
