import Proofs.Erdos85SizeTwoEigenlineEightEightParameterEnumeration
import Proofs.Erdos85SizeTwoEigenlineEightEightLowParameterExclusion

/-!
# Surviving quotient parameters for the `8+8` stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The honest five-way enumeration leaves parameters `2,3,4,5,6`.  The
offset-two midpoint contradiction removes the first two, so downstream
terminal assembly only has to branch on `4,5,6`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- After the low-parameter exclusion, the `8+8` cross quotient is exactly
four, five, or six, with all quotient equations and the surviving sector
information retained. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_survivingParameterEnumeration
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
      (r = 4 ∨ r = 5 ∨ r = 6) ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 7 - r ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = r ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = r ∧
      componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 7 - r ∧
      ((r ≤ 5) ∨
        (r = 6 ∧
          (∀ x : c.supp, x ∈ a.supp →
            (triangleFreeEdgeGraph G).degree x.1 = 0) ∧
          (∀ x : c.supp, x ∈ b.supp →
            (triangleFreeEdgeGraph G).degree x.1 = 0))) := by
  obtain ⟨r, hr, haa, habq, hbaq, hbb, hsector⟩ :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_parameterEnumeration
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
        u v huinj hvinj hurange hvrange hu hv
  have hrSurvive : r = 4 ∨ r = 5 ∨ r = 6 := by
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exfalso
      rcases hsector with hlow | hmid | hhigh
      · exact binarySquare_regular_sizeTwoPart_eight_eightEight_lowParameter_false
          G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a u huinj
            hurange hu hlow.2.1 5 (Or.inr rfl) (by simpa using haa)
      · omega
      · omega
    · exfalso
      rcases hsector with hlow | hmid | hhigh
      · exact binarySquare_regular_sizeTwoPart_eight_eightEight_lowParameter_false
          G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a u huinj
            hurange hu hlow.2.1 4 (Or.inl rfl) (by simpa using haa)
      · omega
      · omega
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  refine ⟨r, hrSurvive, haa, habq, hbaq, hbb, ?_⟩
  rcases hsector with hlow | hmid | hhigh
  · left; omega
  · left; omega
  · right
    exact ⟨by omega, hhigh.2.1, hhigh.2.2⟩

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_survivingParameterEnumeration
