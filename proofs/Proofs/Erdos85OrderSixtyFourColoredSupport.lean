import Proofs.Erdos85OrderSixtyFourSevenComponentLocal

/-! # Colored support in the seven-component order-64 branch -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the seven-component order-64 branch, every vertex of triangle-free
degree two lies in the unique order-16 defect component.  Consequently the
triangle-free-colored sector has order at most sixteen. -/
theorem orderSixtyFour_seven_defect_components_colorOrder_le_sixteen
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    (Finset.univ.filter fun x : Fin 64 =>
      (triangleFreeEdgeGraph G).degree x = 2).card ≤ 16 := by
  classical
  let D := secondOrderDefectGraph G
  let T := triangleFreeEdgeGraph G
  obtain ⟨c, hc16, _hcLocal, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_local_degrees
      G hfree hmin hcover hcount
  have hsupport : ∀ x : Fin 64, T.degree x = 2 → x ∈ c.supp := by
    intro x hx
    let e := D.connectedComponentMk x
    by_contra hxc
    have hec : e ≠ c := by
      intro heq
      apply hxc
      rw [ConnectedComponent.mem_supp_iff]
      exact heq
    obtain ⟨_he8, heLocal⟩ := hsmall e hec
    have hsubset : T.neighborFinset x ⊆
        (G.neighborFinset x).filter (fun y => D.connectedComponentMk y = e) := by
      intro y hy
      have hTxy : T.Adj x y := (T.mem_neighborFinset x y).mp hy
      have hGxy : G.Adj x y :=
        ((mem_triangleFreeNeighbors G x y).mp
          ((triangleFreeEdgeGraph_adj G x y).mp hTxy)).1
      have hDxy : D.Adj x y := by
        change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x y
        exact Or.inr hTxy
      refine Finset.mem_filter.mpr ⟨(G.mem_neighborFinset x y).mpr hGxy, ?_⟩
      exact (ConnectedComponent.connectedComponentMk_eq_of_adj hDxy).symm
    have hcard := Finset.card_le_card hsubset
    have hTcard : (T.neighborFinset x).card = 2 := by
      rw [T.card_neighborFinset_eq_degree, hx]
    have hecard :
        ((G.neighborFinset x).filter
          (fun y => D.connectedComponentMk y = e)).card = 1 := by
      simpa [D, e] using heLocal x (by
        exact ConnectedComponent.connectedComponentMk_mem)
    omega
  have hfilterSubset :
      (Finset.univ.filter fun x : Fin 64 => T.degree x = 2) ⊆ c.supp.toFinset := by
    intro x hx
    rw [Finset.mem_filter] at hx
    exact Set.mem_toFinset.mpr (hsupport x hx.2)
  calc
    (Finset.univ.filter fun x : Fin 64 =>
        (triangleFreeEdgeGraph G).degree x = 2).card =
        (Finset.univ.filter fun x : Fin 64 => T.degree x = 2).card := by rfl
    _ ≤ c.supp.toFinset.card := Finset.card_le_card hfilterSubset
    _ = c.supp.ncard := (Set.ncard_eq_toFinset_card' c.supp).symm
    _ = 16 := hc16

end

end Erdos85
