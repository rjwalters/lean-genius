import Proofs.Erdos85OrderFortyNineEmptyTriangleCover
import Proofs.Erdos85OrderFortyNineSevenHighT0EmptyEdgeNine

/-! If the actual H7 empty graph has no triangle, at least four all-low
triangles are needed to cover its seven vertices. No empty-edge count or
residual spectrum hypothesis is imposed. -/
namespace Erdos85
open SimpleGraph
noncomputable section

theorem sevenHigh_t0_no_empty_triangle_four_low_triangles
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (htri : ((G.induce (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))).cliqueFinset 3).card = 0) :
    4 ≤ ((G.induce (↑(orderFortyNineLowVertices G) : Set (Fin 49))).cliqueFinset 3).card := by
  classical
  let E := sevenHighT0LowSupportFiber G 0
  let H := G.induce (↑E : Set (Fin 49))
  let L := G.induce (↑(orderFortyNineLowVertices G) : Set (Fin 49))
  have hcardE : E.card = 7 := by
    have hcensus := sevenHigh_t0_global_incidence G hfree hmin hHigh hzero
    simpa [E, sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.1
  let f : (↑E : Set (Fin 49)) ↪ (↑(orderFortyNineLowVertices G) : Set (Fin 49)) :=
    ⟨fun x => ⟨x.val, (Finset.mem_filter.mp x.property).1⟩,
      fun x y h => Subtype.ext (congrArg
        (fun z : (↑(orderFortyNineLowVertices G) : Set (Fin 49)) => z.val) h)⟩
  let S := Finset.univ.map f
  have hS : S.card = 7 := by simpa [S] using hcardE
  have hcover : ∀ x ∈ S, ∃ t ∈ L.cliqueFinset 3, x ∈ t := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
    apply orderFortyNine_empty_low_vertex_mem_triangle G hfree hmin (by decide)
    have hempty := (Finset.mem_filter.mp y.property).2
    simpa [f, orderFortyNineHighSupport] using hempty
  have hcap : ∀ t ∈ L.cliqueFinset 3, (S ∩ t).card ≤ 2 := by
    intro t ht
    have hc := L.mem_cliqueFinset_iff.mp ht
    by_contra hn
    have hle := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := t))
    have heq : S ∩ t = t := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_right (by have := hc.card_eq; omega)
    have htS : t ⊆ S := by rw [← heq]; exact Finset.inter_subset_left
    obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := SimpleGraph.is3Clique_iff.mp hc
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp (htS (by simp : u ∈ ({u,v,w} : Finset _)))
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp (htS (by simp : v ∈ ({f x,v,w} : Finset _)))
    obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp (htS (by simp : w ∈ ({f x,f y,w} : Finset _)))
    have hclique : H.IsNClique 3 {x,y,z} :=
      SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, huw, hvw⟩
    have hmem := H.mem_cliqueFinset_iff.mpr hclique
    have hempty : H.cliqueFinset 3 = ∅ := Finset.card_eq_zero.mp htri
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  have hsub : S ⊆ (L.cliqueFinset 3).biUnion (fun t => S ∩ t) := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_inter.mpr ⟨hx,hxt⟩⟩
  have hbound := (Finset.card_le_card hsub).trans
    (Finset.card_biUnion_le_card_mul (L.cliqueFinset 3) (fun t => S ∩ t) 2 hcap)
  change 4 ≤ (L.cliqueFinset 3).card
  omega

end
end Erdos85
#print axioms Erdos85.sevenHigh_t0_no_empty_triangle_four_low_triangles
