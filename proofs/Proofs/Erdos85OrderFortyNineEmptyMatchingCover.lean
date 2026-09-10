import Proofs.Erdos85OrderFortyNineEmptyTriangleCover
import Proofs.Erdos85TriangleMatchingCover

/-! Actual empty-support triangle covers, with a known family and a matching bound. -/
namespace Erdos85
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

/-- The known triangles and the vertices they avoid contribute separately;
only a disjoint edge family in S can save triangles in the remaining cover. -/
theorem orderFortyNine_empty_matching_triangle_cover_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (S : Finset (↑(orderFortyNineLowVertices G) : Set V))
    (known : Finset (Finset (↑(orderFortyNineLowVertices G) : Set V)))
    (ν : ℕ)
    (hempty : ∀ x ∈ S,
      (G.neighborFinset x.val ∩ orderFortyNineHighVertices G).card = 0)
    (hknown : known ⊆ (G.induce (↑(orderFortyNineLowVertices G) : Set V)).cliqueFinset 3)
    (havoid : ∀ t ∈ known, Disjoint S t)
    (hcap : ∀ t ∈ (G.induce (↑(orderFortyNineLowVertices G) : Set V)).cliqueFinset 3,
      t ∉ known → (S ∩ t).card ≤ 2)
    (hmatching : ∀ P : Finset (Finset (↑(orderFortyNineLowVertices G) : Set V)),
      (∀ e ∈ P,
        (G.induce (↑(orderFortyNineLowVertices G) : Set V)).IsNClique 2 e ∧ e ⊆ S) →
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
  have h := triangle_cover_bound_of_disjoint_pair_bound L S rest ν
    Finset.sdiff_subset hcover
    (fun t ht => hcap t (Finset.mem_sdiff.mp ht).1 (Finset.mem_sdiff.mp ht).2)
    hmatching
  have hrest : rest.card = (L.cliqueFinset 3).card - known.card :=
    Finset.card_sdiff_of_subset hknown
  have hle : known.card ≤ (L.cliqueFinset 3).card := Finset.card_le_card hknown
  change known.card + S.card ≤ (L.cliqueFinset 3).card + ν
  rw [hrest] at h
  omega

end
end Erdos85
#print axioms Erdos85.orderFortyNine_empty_matching_triangle_cover_bound
