import Proofs.Erdos85SecondOrderQuotient

/-!
# Color support in the order-64 seven-component branch

A triangle-free-colored vertex has two ambient neighbors joined to it by
edges of the second-order defect graph.  Hence it cannot lie in a defect
component where its total number of ambient neighbors inside that component
is at most one.  In the `16 + 6 * 8` branch, all colored vertices are
therefore supported on the unique order-16 component.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If every vertex outside one order-16 defect component has at most one
ambient neighbor in its own defect component, the triangle-free color order
is at most sixteen. -/
theorem orderSixtyFour_colorOrder_le_sixteen_of_smallComponent_localDegree
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16)
    (hsmall : ∀ x : Fin 64,
      (secondOrderDefectGraph G).connectedComponentMk x ≠ c →
        (componentNeighborFinset G (secondOrderDefectGraph G)
          ((secondOrderDefectGraph G).connectedComponentMk x) x).card ≤ 1) :
    ((Finset.univ.filter fun x : Fin 64 =>
      (triangleFreeEdgeGraph G).degree x = 2).card) ≤ 16 := by
  classical
  let D := secondOrderDefectGraph G
  have hsupport :
      (Finset.univ.filter fun x : Fin 64 =>
        (triangleFreeEdgeGraph G).degree x = 2) ⊆
      Finset.univ.filter fun x : Fin 64 => D.connectedComponentMk x = c := by
    intro x hx
    have hxdegree : (triangleFreeEdgeGraph G).degree x = 2 :=
      (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩
    by_contra hxc
    have hsubset : (triangleFreeEdgeGraph G).neighborFinset x ⊆
        componentNeighborFinset G D (D.connectedComponentMk x) x := by
      intro y hy
      have ht : (triangleFreeEdgeGraph G).Adj x y :=
        (triangleFreeEdgeGraph G).mem_neighborFinset x y |>.mp hy
      have hG : G.Adj x y :=
        (mem_triangleFreeNeighbors G x y).mp ht |>.1
      have hD : D.Adj x y := by
        exact (show (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x y from
          Or.inr ht)
      have hcomp : D.connectedComponentMk y = D.connectedComponentMk x :=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hD).symm
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset x y).mpr hG, hcomp⟩
    have htwo : ((triangleFreeEdgeGraph G).neighborFinset x).card = 2 := by
      rw [(triangleFreeEdgeGraph G).card_neighborFinset_eq_degree, hxdegree]
    have hle := Finset.card_le_card hsubset
    have hone := hsmall x hxc
    dsimp only [D] at hle
    omega
  calc
    ((Finset.univ.filter fun x : Fin 64 =>
        (triangleFreeEdgeGraph G).degree x = 2).card) ≤
        (Finset.univ.filter fun x : Fin 64 =>
          D.connectedComponentMk x = c).card :=
      Finset.card_le_card hsupport
    _ = c.supp.ncard := by
      dsimp only [D]
      rw [← Set.ncard_coe_finset]
      congr 1
      ext x
      simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
    _ = 16 := hc

end

end Erdos85
