import Proofs.Erdos85SizeTwoEigenlineSixTenCrossSignCoordinates

/-!
# A forced antipodal triangle in the q=8 six-plus-ten stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

Choose a same-sign diagonal defect neighbor of a vertex on the ten-cycle and
a cross-defect neighbor on the six-cycle.  Cross checkerboard saturation makes
the third defect edge automatic.  The cross edges cannot be ambient edges
because they join distinct ambient components, while the diagonal edge cannot
be ambient because ambient cycle edges flip the eigenline sign.  Hence all
three edges are antipodal.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private theorem antipodal_adj_of_secondOrderDefect_adj_of_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} (hD : (secondOrderDefectGraph G).Adj x y)
    (hnot : ¬ G.Adj x y) :
    (antipodalGraph G).Adj x y := by
  change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x y at hD
  rcases hD with hanti | htf
  · exact hanti
  · exact False.elim (hnot
      ((mem_triangleFreeNeighbors G x y).mp
        ((triangleFreeEdgeGraph_adj G x y).mp htf)).1)

/-- The `6+10` size-two eigenline stratum contains three vertices spanning a
triangle in the antipodal graph, with one vertex on the six-cycle and two on
the ten-cycle. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_exists_antipodalTriangle
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
    ∃ x y z : c.supp,
      x ∈ a.supp ∧ y ∈ b.supp ∧ z ∈ b.supp ∧
      (antipodalGraph G).Adj x.1 y.1 ∧
      (antipodalGraph G).Adj y.1 z.1 ∧
      (antipodalGraph G).Adj z.1 x.1 := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let y := v 0
  have hy : y ∈ b.supp := by
    rw [← hvrange]
    exact ⟨0, rfl⟩
  have hdiag :=
    (binarySquare_regular_sizeTwoPart_eight_sixTen_longDiagonal_signSplit
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb y hy).1
  have hdiagNonempty :
      ((componentNeighborFinset K H b y).filter
        fun z => s z.1 = s y.1).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hdiag
    simp at hdiag
  obtain ⟨z, hz⟩ := hdiagNonempty
  have hzKmem := (Finset.mem_filter.mp hz).1
  have hzsign : s z.1 = s y.1 := (Finset.mem_filter.mp hz).2
  have hzb : z ∈ b.supp :=
    (ConnectedComponent.mem_supp_iff b z).mpr (Finset.mem_filter.mp hzKmem).2
  have hyzK : K.Adj y z :=
    (K.mem_neighborFinset y z).mp (Finset.mem_filter.mp hzKmem).1
  have hcross :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_longVertex_three_sameSign_cross
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb y hy
  have hcrossNonempty :
      ((componentNeighborFinset K H a y).filter
        fun x => s x.1 = s y.1).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hcross
    simp at hcross
  obtain ⟨x, hx⟩ := hcrossNonempty
  have hxKmem := (Finset.mem_filter.mp hx).1
  have hxsign : s x.1 = s y.1 := (Finset.mem_filter.mp hx).2
  have hxa : x ∈ a.supp :=
    (ConnectedComponent.mem_supp_iff a x).mpr (Finset.mem_filter.mp hxKmem).2
  have hyxK : K.Adj y x :=
    (K.mem_neighborFinset y x).mp (Finset.mem_filter.mp hxKmem).1
  obtain ⟨i, rfl⟩ : ∃ i, u i = x := by
    have hxrange : x ∈ Set.range u := by
      rw [hurange]
      exact hxa
    exact hxrange
  obtain ⟨j, rfl⟩ : ∃ j, v j = z := by
    have hzrange : z ∈ Set.range v := by
      rw [hvrange]
      exact hzb
    exact hzrange
  have hxzK : K.Adj (u i) (v j) :=
    (binarySquare_regular_sizeTwoPart_eight_sixTen_crossDefect_iff_sign_eq_of_coordinates
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        u v huinj hvinj hurange hvrange hu hv i j).2 (hzsign.trans hxsign.symm)
  have hnotGxy : ¬ G.Adj (u i).1 y.1 := by
    intro hG
    have hH : H.Adj (u i) y := hG
    have hab : a = b := by
      rw [← (ConnectedComponent.mem_supp_iff a (u i)).mp hxa,
        ← (ConnectedComponent.mem_supp_iff b y).mp hy]
      exact ConnectedComponent.connectedComponentMk_eq_of_adj hH
    rw [hab] at ha
    omega
  have hnotGxz : ¬ G.Adj (u i).1 (v j).1 := by
    intro hG
    have hH : H.Adj (u i) (v j) := hG
    have hab : a = b := by
      rw [← (ConnectedComponent.mem_supp_iff a (u i)).mp hxa,
        ← (ConnectedComponent.mem_supp_iff b (v j)).mp hzb]
      exact ConnectedComponent.connectedComponentMk_eq_of_adj hH
    rw [hab] at ha
    omega
  have hnotGyz : ¬ G.Adj y.1 (v j).1 := by
    intro hG
    have hzmem : (v j).1 ∈
        componentNeighborFinset G (secondOrderDefectGraph G) c y.1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset y.1 (v j).1).mpr hG, (v j).2⟩
    have hflip := (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hA_in y.2).2 (v j).1 hzmem
    rcases hs_in y.1 y.2 with hyneg | hypos <;> omega
  have hxyAnti : (antipodalGraph G).Adj (u i).1 y.1 :=
    antipodal_adj_of_secondOrderDefect_adj_of_not_adj G hyxK.symm hnotGxy
  have hyzAnti : (antipodalGraph G).Adj y.1 (v j).1 :=
    antipodal_adj_of_secondOrderDefect_adj_of_not_adj G hyzK hnotGyz
  have hzxAnti : (antipodalGraph G).Adj (v j).1 (u i).1 :=
    antipodal_adj_of_secondOrderDefect_adj_of_not_adj G hxzK.symm
      (fun h => hnotGxz h.symm)
  exact ⟨u i, y, v j, hxa, hy, hzb, hxyAnti, hyzAnti, hzxAnti⟩

/-- Every same-sign diagonal defect edge on the ten-cycle is the base of
exactly the three antipodal triangles supplied by the six-cycle neighbors of
its first endpoint. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_sameSignDiagonal_three_antipodalTriangles
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
      {v (z - 1), v (z + 1)})
    (i j : ZMod 10)
    (hijK : ((secondOrderDefectGraph G).induce c.supp).Adj (v i) (v j))
    (hijSign : s (v j).1 = s (v i).1) :
    (antipodalGraph G).Adj (v i).1 (v j).1 ∧
      (((componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a (v i)).filter
        fun x => (antipodalGraph G).Adj x.1 (v i).1 ∧
          (antipodalGraph G).Adj x.1 (v j).1).card = 3) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hvi : v i ∈ b.supp := by
    rw [← hvrange]
    exact ⟨i, rfl⟩
  have hvj : v j ∈ b.supp := by
    rw [← hvrange]
    exact ⟨j, rfl⟩
  have hnotGij : ¬ G.Adj (v i).1 (v j).1 := by
    intro hG
    have hjmem : (v j).1 ∈
        componentNeighborFinset G (secondOrderDefectGraph G) c (v i).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset (v i).1 (v j).1).mpr hG, (v j).2⟩
    have hflip := (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hA_in (v i).2).2 (v j).1 hjmem
    rcases hs_in (v i).1 (v i).2 with hineg | hipos <;> omega
  refine ⟨antipodal_adj_of_secondOrderDefect_adj_of_not_adj G hijK hnotGij, ?_⟩
  have hsignCard :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_longVertex_three_sameSign_cross
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb (v i) hvi
  rw [← hsignCard]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, _hxi, _hxj⟩
    have hxa : x ∈ a.supp :=
      (ConnectedComponent.mem_supp_iff a x).mpr (Finset.mem_filter.mp hx).2
    have hxiK : K.Adj x (v i) :=
      ((K.mem_neighborFinset (v i) x).mp (Finset.mem_filter.mp hx).1).symm
    exact ⟨hx,
      binarySquare_regular_sizeTwoPart_eight_sixTen_cross_defect_preserves_sign
        G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
          x (v i) hxa hvi hxiK |>.symm⟩
  · rintro ⟨hx, hxsign⟩
    have hxa : x ∈ a.supp :=
      (ConnectedComponent.mem_supp_iff a x).mpr (Finset.mem_filter.mp hx).2
    have hxiK : K.Adj x (v i) :=
      ((K.mem_neighborFinset (v i) x).mp (Finset.mem_filter.mp hx).1).symm
    have hxrange : x ∈ Set.range u := by
      rw [hurange]
      exact hxa
    obtain ⟨k, rfl⟩ := hxrange
    have hxjK : K.Adj (u k) (v j) :=
      (binarySquare_regular_sizeTwoPart_eight_sixTen_crossDefect_iff_sign_eq_of_coordinates
        G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
          u v huinj hvinj hurange hvrange hu hv k j).2
        (hijSign.trans hxsign.symm)
    have hnotGxi : ¬ G.Adj (u k).1 (v i).1 := by
      intro hG
      have hH : H.Adj (u k) (v i) := hG
      have hab : a = b := by
        rw [← (ConnectedComponent.mem_supp_iff a (u k)).mp hxa,
          ← (ConnectedComponent.mem_supp_iff b (v i)).mp hvi]
        exact ConnectedComponent.connectedComponentMk_eq_of_adj hH
      rw [hab] at ha
      omega
    have hnotGxj : ¬ G.Adj (u k).1 (v j).1 := by
      intro hG
      have hH : H.Adj (u k) (v j) := hG
      have hab : a = b := by
        rw [← (ConnectedComponent.mem_supp_iff a (u k)).mp hxa,
          ← (ConnectedComponent.mem_supp_iff b (v j)).mp hvj]
        exact ConnectedComponent.connectedComponentMk_eq_of_adj hH
      rw [hab] at ha
      omega
    exact ⟨hx,
      antipodal_adj_of_secondOrderDefect_adj_of_not_adj G hxiK hnotGxi,
      antipodal_adj_of_secondOrderDefect_adj_of_not_adj G hxjK hnotGxj⟩

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_exists_antipodalTriangle
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_sameSignDiagonal_three_antipodalTriangles
