import Proofs.Erdos85SizeTwoEigenlineEightEightHighParameterSix

/-!
# Exhaustive quotient-parameter enumeration for the eight-plus-eight stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The sector trichotomy initially leaves the cross quotient in `[2,7]`.
Cyclic coordinates and the size-two eigenline ledger exclude seven, leaving
exactly the five parameters `2,3,4,5,6`.  This is the honest interface for
downstream branch assembly: in particular, parameters two and three are not
silently folded into the parameter-four owner model.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The two-cycle `8+8` quotient has one of exactly five parameter values.
The accompanying sector conclusion records that parameters two and three
are both-all-triangle-free, while parameter six is both-all-triangle. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterEnumeration
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
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    ∃ r : ℕ,
      (r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6) ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 7 - r ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = r ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = r ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 7 - r ∧
      ((r ≤ 3 ∧
          (∀ x : c.supp, x ∈ a.supp →
            (triangleFreeEdgeGraph G).degree x.1 = 2) ∧
          (∀ x : c.supp, x ∈ b.supp →
            (triangleFreeEdgeGraph G).degree x.1 = 2)) ∨
        (4 ≤ r ∧ r ≤ 5) ∨
        (r = 6 ∧
          (∀ x : c.supp, x ∈ a.supp →
            (triangleFreeEdgeGraph G).degree x.1 = 0) ∧
          (∀ x : c.supp, x ∈ b.supp →
            (triangleFreeEdgeGraph G).degree x.1 = 0))) := by
  obtain ⟨r, hr2, hr7, haa, habq, hbaq, hbb, hsector⟩ :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_sectorTrichotomy
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb hab
  have hrne7 : r ≠ 7 := by
    intro hr
    apply binarySquare_regular_sizeTwoPart_eight_eightEight_crossQuotient_ne_seven_of_coordinates
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        u v huinj hvinj hurange hvrange hu hv
    simpa [hr] using habq
  have hr6 : r ≤ 6 := by omega
  refine ⟨r, by omega, haa, habq, hbaq, hbb, ?_⟩
  rcases hsector with hlow | hmid | hhigh
  · exact Or.inl hlow
  · exact Or.inr (Or.inl hmid)
  · exact Or.inr (Or.inr ⟨by omega, hhigh.2.1, hhigh.2.2⟩)

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameterEnumeration
