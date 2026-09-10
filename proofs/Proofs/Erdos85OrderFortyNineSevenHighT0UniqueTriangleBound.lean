import Proofs.Erdos85OrderFortyNineEmptyTriangleCover
import Proofs.Erdos85OrderFortyNineSevenHighT0EmptyDegreeProfile
import Proofs.Erdos85SevenVertexUniqueTriangle

/-!
# Four all-low triangles at the H7 unique-empty-triangle endpoint

The degree-two vertices of the nine-edge empty graph form an independent
three-set avoiding its unique triangle. Actual empty-support coverage then
requires three additional all-low triangles. No residual spectrum is assumed.
-/
namespace Erdos85
open SimpleGraph
noncomputable section

/-- The actual H7/T0 nine-edge endpoint with exactly one empty triangle
has at least four all-low triangles. -/
theorem sevenHigh_t0_unique_empty_triangle_four_low_triangles
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (hedges : sevenHighT0InternalEdgeCount G 0 = 9)
    (htri : ((G.induce (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))).cliqueFinset 3).card = 1) :
    4 ≤ ((G.induce (↑(orderFortyNineLowVertices G) : Set (Fin 49))).cliqueFinset 3).card := by
  classical
  let E := sevenHighT0LowSupportFiber G 0
  let H := G.induce (↑E : Set (Fin 49))
  let L := G.induce (↑(orderFortyNineLowVertices G) : Set (Fin 49))
  have hcardE : E.card = 7 := by
    have hcensus := sevenHigh_t0_global_incidence G hfree hmin hHigh hzero
    simpa [E, sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.1
  have hcard : Fintype.card (↑E : Set (Fin 49)) = 7 := by simpa using hcardE
  let S := Finset.univ.filter (fun x => H.degree x = 2)
  obtain ⟨hS, hind, havoid⟩ :=
    sevenVertex_uniqueTriangle_independent_three_avoiding_triangle H
      (not_containsC4_induce_finset G hfree E) hcard
      (sevenHigh_t0_empty_induce_degree_le_three G hfree hmin hHigh hzero)
      hedges htri
  change S.card = 3 at hS
  change (H.cliqueFinset 3).card = 1 at htri
  have hnonempty : (H.cliqueFinset 3).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨t, ht⟩ := hnonempty
  let f : (↑E : Set (Fin 49)) ↪ (↑(orderFortyNineLowVertices G) : Set (Fin 49)) :=
    ⟨fun x => ⟨x.val, (Finset.mem_filter.mp x.property).1⟩,
      fun x y h => Subtype.ext (congrArg
        (fun z : (↑(orderFortyNineLowVertices G) : Set (Fin 49)) => z.val) h)⟩
  have hclique : L.IsNClique 3 (t.map f) := by
    have hc := H.mem_cliqueFinset_iff.mp ht
    obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := SimpleGraph.is3Clique_iff.mp hc
    simpa using (SimpleGraph.is3Clique_triple_iff.mpr
      (show L.Adj (f u) (f v) ∧ L.Adj (f u) (f w) ∧ L.Adj (f v) (f w) from
        ⟨huv, huw, hvw⟩))
  have hbound := orderFortyNine_empty_independent_triangle_cover_bound
    G hfree hmin (by decide) (S.map f) {t.map f}
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      have hempty := (Finset.mem_filter.mp y.property).2
      simpa [f, orderFortyNineHighSupport] using hempty)
    (by
      intro u hu v hv hne huv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hv
      exact hind x hx y hy (fun h => hne (congrArg f h)) huv)
    (by
      intro s hs
      have hs' := Finset.mem_singleton.mp hs
      subst s
      exact L.mem_cliqueFinset_iff.mpr hclique)
    (by
      intro s hs
      have hs' := Finset.mem_singleton.mp hs
      subst s
      apply Finset.disjoint_left.mpr
      intro x hx hxt
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨v, hv, heq⟩ := Finset.mem_map.mp hxt
      have huv : v = u := f.injective heq
      subst v
      exact Finset.disjoint_left.mp (havoid t ht) hu hv)
  simpa [hS] using hbound

end
end Erdos85
#print axioms Erdos85.sevenHigh_t0_unique_empty_triangle_four_low_triangles
