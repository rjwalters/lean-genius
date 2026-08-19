import Proofs.Erdos85SizeTwoEigenlineEightEightParameterFourSectorCases

/-!
# Exhaustive terminal assembly for the `8+8` stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

This capstone isolates the four concrete terminal sockets.  The structural
tree has already reduced the quotient to `r=4` or `r=6`; parameter four has
the low, mixed, and both-triangle shore cases, while parameter six is wholly
all-triangle.  Supplying a contradiction for each socket closes the entire
`8+8` stratum.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A shore of a size-two component is wholly all-triangle-free. -/
def EightEightShoreAllTf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (a : (G.induce c.supp).ConnectedComponent) : Prop :=
  ∀ x : c.supp, x ∈ a.supp → (triangleFreeEdgeGraph G).degree x.1 = 2

/-- A shore of a size-two component is wholly all-triangle. -/
def EightEightShoreAllTriangle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (a : (G.induce c.supp).ConnectedComponent) : Prop :=
  ∀ x : c.supp, x ∈ a.supp → (triangleFreeEdgeGraph G).degree x.1 = 0

/-- Abstract exhaustive terminal assembly.  Each callback is exactly one
graph-facing owner-certificate socket. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_false_of_terminals
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
      {v (z - 1), v (z + 1)})
    (h4low : componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 4 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 4 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 3 →
      EightEightShoreAllTf G c a → EightEightShoreAllTf G c b → False)
    (h4mixed : componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 4 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 4 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 3 →
      ((EightEightShoreAllTf G c a ∧ EightEightShoreAllTriangle G c b) ∨
       (EightEightShoreAllTriangle G c a ∧ EightEightShoreAllTf G c b)) → False)
    (h4both : componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 4 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 4 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 3 →
      EightEightShoreAllTriangle G c a →
      EightEightShoreAllTriangle G c b → False)
    (h6 : componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 1 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 6 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 6 →
      componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 1 →
      EightEightShoreAllTriangle G c a →
      EightEightShoreAllTriangle G c b → False) :
    False := by
  obtain ⟨r, hr, haa, habq, hbaq, hbb, hsector⟩ :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_survivingParameterEnumeration
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
        u v huinj hvinj hurange hvrange hu hv
  rcases hr with rfl | rfl
  · have hcases :=
      binarySquare_regular_sizeTwoPart_eight_eightEight_parameterFour_sectorCases
        G hfree hreg hcard c hc a b
    rcases hcases with hlow | hmixed | hboth
    · exact h4low (by omega) habq hbaq (by omega) hlow.1 hlow.2
    · exact h4mixed (by omega) habq hbaq (by omega) hmixed
    · exact h4both (by omega) habq hbaq (by omega) hboth.1 hboth.2
  · rcases hsector with hle | hhigh
    · omega
    · exact h6 (by omega) habq hbaq (by omega) hhigh.2.1 hhigh.2.2

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_false_of_terminals
