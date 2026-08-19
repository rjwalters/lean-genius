import Proofs.Erdos85SizeTwoEigenlineSixTenCrossSignCoordinates

/-!
# Antipodal color of the q=8 six-by-ten cross block

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

Vertices on the two ambient cycle components cannot be adjacent in the
ambient graph.  Therefore every cross defect edge is antipodal, and the
already-classified sign checkerboard is the exact antipodal cross block.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In cyclic coordinates on the `6+10` stratum, cross antipodal adjacency is
equivalent to equality of eigenline signs. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_crossAntipodal_iff_sign_eq_of_coordinates
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    ∀ i j,
      (antipodalGraph G).Adj (u i).1 (v j).1 ↔
        s (v j).1 = s (u i).1 := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hua : ∀ i, u i ∈ a.supp := by
    intro i
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hvb : ∀ j, v j ∈ b.supp := by
    intro j
    rw [← hvrange]
    exact ⟨j, rfl⟩
  have hnotG : ∀ i j, ¬ G.Adj (u i).1 (v j).1 := by
    intro i j hG
    have hH : H.Adj (u i) (v j) := hG
    have hab : a = b := by
      rw [← (ConnectedComponent.mem_supp_iff a (u i)).mp (hua i),
        ← (ConnectedComponent.mem_supp_iff b (v j)).mp (hvb j)]
      exact ConnectedComponent.connectedComponentMk_eq_of_adj hH
    rw [hab] at ha
    omega
  intro i j
  constructor
  · intro hanti
    have hK : K.Adj (u i) (v j) := by
      change (secondOrderDefectGraph G).Adj (u i).1 (v j).1
      change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj
        (u i).1 (v j).1
      exact Or.inl hanti
    exact (binarySquare_regular_sizeTwoPart_eight_sixTen_crossDefect_iff_sign_eq_of_coordinates
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        u v huinj hvinj hurange hvrange hu hv i j).1 hK
  · intro hsign
    have hK : K.Adj (u i) (v j) :=
      (binarySquare_regular_sizeTwoPart_eight_sixTen_crossDefect_iff_sign_eq_of_coordinates
        G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
          u v huinj hvinj hurange hvrange hu hv i j).2 hsign
    change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj
      (u i).1 (v j).1 at hK
    rcases hK with hanti | htf
    · exact hanti
    · exact False.elim ((hnotG i j)
        ((mem_triangleFreeNeighbors G (u i).1 (v j).1).mp
          ((triangleFreeEdgeGraph_adj G (u i).1 (v j).1).mp htf)).1)

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_crossAntipodal_iff_sign_eq_of_coordinates
