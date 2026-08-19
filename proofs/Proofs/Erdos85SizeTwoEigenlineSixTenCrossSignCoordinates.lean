import Proofs.Erdos85SizeTwoEigenlineSixTenCheckerboard
import Proofs.Erdos85SizeTwoEigenlineSixTenCrossSign

/-!
# Sign form of the q=8 six-plus-ten checkerboard

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The graph-facing checkerboard and the alternating eigenline both flip on
every unit step of either internal cycle.  Since cross adjacency already
implies equal signs, the two colorings have the same phase: in cyclic
coordinates, cross-defect adjacency is equivalent to eigenline-sign equality.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private theorem zmodTen_flippingPredicate_iff_flippingSign
    (P : ZMod 10 → Prop) [DecidablePred P]
    (g : ZMod 10 → ℤ) (h : ℤ)
    (hP : ∀ j, P (j + 1) ↔ ¬ P j)
    (hg : ∀ j, g (j + 1) = -g j)
    (hgsign : ∀ j, g j = -1 ∨ g j = 1)
    (hforward : ∀ j, P j → g j = h) :
    ∀ j, P j ↔ g j = h := by
  have hp0 := hP 0
  norm_num at hp0
  have hhsign : h = -1 ∨ h = 1 := by
    by_cases h0 : P 0
    · rw [← hforward 0 h0]
      exact hgsign 0
    · have h1 : P 1 := hp0.mpr h0
      rw [← hforward 1 h1]
      exact hgsign 1
  have allCases : ∀ z : ZMod 10, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨
      z = 5 ∨ z = 6 ∨ z = 7 ∨ z = 8 ∨ z = 9 := by
    decide
  have hbase : P 0 ↔ g 0 = h := by
    constructor
    · exact hforward 0
    · intro h0
      by_contra hnP0
      have hP1 : P 1 := hp0.mpr hnP0
      have hg1h := hforward 1 hP1
      have hg01 := hg 0
      norm_num at hg01
      rcases hgsign 0 with hg0neg | hg0pos <;> omega
  have hstep (j : ZMod 10) (hj : P j ↔ g j = h) :
      P (j + 1) ↔ g (j + 1) = h := by
    rw [hP j, hg j]
    rcases hgsign j with hjneg | hjpos <;>
      rcases hhsign with hhneg | hhpos <;> simp_all
  have h1 := hstep 0 hbase
  have h2 := hstep 1 h1
  have h3 := hstep 2 h2
  have h4 := hstep 3 h3
  have h5 := hstep 4 h4
  have h6 := hstep 5 h5
  have h7 := hstep 6 h6
  have h8 := hstep 7 h7
  have h9 := hstep 8 h8
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9
  intro j
  have hjCases := allCases j
  rcases hjCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    assumption

/-- In cyclic coordinates on the `6+10` stratum, cross-defect adjacency is
exactly equality of the alternating eigenline signs. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_crossDefect_iff_sign_eq_of_coordinates
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
      ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (v j) ↔
        s (v j).1 = s (u i).1 := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  obtain ⟨htarget, _hsource⟩ :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_crossDefect_checkerboard_of_coordinates
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb
        u v huinj hvinj hurange hvrange hu hv
  have hvsign : ∀ j : ZMod 10, s (v (j + 1)).1 = -s (v j).1 := by
    intro j
    have hH : H.Adj (v j) (v (j + 1)) := by
      rw [← H.mem_neighborFinset, hv]
      simp
    have hmem : (v (j + 1)).1 ∈
        componentNeighborFinset G (secondOrderDefectGraph G) c (v j).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hH, (v (j + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hA_in (v j).2).2 _ hmem
  intro i
  let P : ZMod 10 → Prop := fun j => K.Adj (u i) (v j)
  have hP : ∀ j, P (j + 1) ↔ ¬ P j := htarget i
  have hforward : ∀ j, P j → s (v j).1 = s (u i).1 := by
    intro j hij
    exact binarySquare_regular_sizeTwoPart_eight_sixTen_cross_defect_preserves_sign
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        (u i) (v j) (by rw [← hurange]; exact ⟨i, rfl⟩)
        (by rw [← hvrange]; exact ⟨j, rfl⟩) hij
  exact zmodTen_flippingPredicate_iff_flippingSign P
    (fun j => s (v j).1) (s (u i).1) hP hvsign
    (fun j => hs_in _ (v j).2) hforward

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_crossDefect_iff_sign_eq_of_coordinates
