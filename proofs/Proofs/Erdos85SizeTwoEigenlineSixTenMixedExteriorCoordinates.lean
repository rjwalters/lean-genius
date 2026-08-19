import Proofs.Erdos85SizeTwoEigenlineSixTenCrossSignCoordinates
import Proofs.Erdos85ExteriorPairGraphAdjacency

/-!
# Cross exterior-pair coordinates in the genuine mixed C6+C10 branch

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The short and long cycles are distinct ambient connected components, so a
cross pair is neither ambient-adjacent nor joined by an internal common
neighbor.  The exterior-pair relation is therefore the complement of the
already classified cross defect checkerboard: precisely the opposite-sign
pairs.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In cyclic coordinates on the genuine `6+10` stratum, a cross pair is an
exterior pair exactly when its eigenline signs are opposite. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_crossExteriorPair_iff_sign_neg
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
    ∀ i j, (exteriorPairGraph G c.supp).Adj (u i) (v j) ↔
      s (v j).1 = -s (u i).1 := by
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
  have hab : a ≠ b := by
    intro h
    rw [h] at ha
    omega
  have huv : ∀ i j, u i ≠ v j := by
    intro i j h
    apply hab
    rw [← (ConnectedComponent.mem_supp_iff a (u i)).mp (hua i),
      ← (ConnectedComponent.mem_supp_iff b (v j)).mp (hvb j), h]
  have hcommon : ∀ i j, ¬ ∃ z : c.supp,
      G.Adj (u i).1 z.1 ∧ G.Adj (v j).1 z.1 := by
    rintro i j ⟨z, huz, hvz⟩
    have hHu : H.Adj (u i) z := huz
    have hHv : H.Adj (v j) z := hvz
    apply hab
    rw [← (ConnectedComponent.mem_supp_iff a (u i)).mp (hua i),
      ← (ConnectedComponent.mem_supp_iff b (v j)).mp (hvb j)]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj hHu).trans
      (ConnectedComponent.connectedComponentMk_eq_of_adj hHv).symm
  intro i j
  have hD : K.Adj (u i) (v j) ↔ s (v j).1 = s (u i).1 :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_crossDefect_iff_sign_eq_of_coordinates
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        u v huinj hvinj hurange hvrange hu hv i j
  rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common
    G hfree c (u i) (v j)]
  change u i ≠ v j ∧ ¬ K.Adj (u i) (v j) ∧
    ¬ (∃ z : c.supp, G.Adj (u i).1 z.1 ∧ G.Adj (v j).1 z.1) ↔ _
  rw [and_iff_right (huv i j), and_iff_left (hcommon i j), hD]
  rcases hs_in (u i).1 (u i).2 with huNeg | huPos <;>
    rcases hs_in (v j).1 (v j).2 with hvNeg | hvPos <;> simp_all

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_crossExteriorPair_iff_sign_neg
