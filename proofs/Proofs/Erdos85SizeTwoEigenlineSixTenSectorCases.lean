import Proofs.Erdos85SizeTwoEigenlineAllTriangleCycleDiagonal

/-!
# The two sector cases of the 6+10 stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3 (assembly skeleton).

The short hexagon of a 6+10 component is forced all-triangle-free, and
the internal-cycle sector dichotomy splits the long decagon into
all-triangle or all-triangle-free.  So the stratum decomposes into
exactly the two hypothesis packages carried by the checked owner
terminals: MIXED (short all-TF + long all-triangle) and BOTH-ALL-TF.
The eventual 6+10 capstone is this theorem composed with the two
`…ConstraintSemantics_false` terminals through their model packages.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- **6+10 sector cases.**  The short shore is always all-triangle-free,
and the long shore is either all-triangle (the mixed branch) or
all-triangle-free (the both-all-TF branch). -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_sector_cases
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
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) :
    (∀ x : c.supp, x ∈ a.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 2) ∧
      ((∀ z : c.supp, z ∈ b.supp →
          (triangleFreeEdgeGraph G).degree z.1 = 0) ∨
        (∀ z : c.supp, z ∈ b.supp →
          (triangleFreeEdgeGraph G).degree z.1 = 2)) :=
  ⟨binarySquare_regular_sizeTwoPart_eight_sixTen_shortCycle_allTriangleFree
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb,
    binarySquare_regular_sizeTwoPart_internalCycle_sector_dichotomy
      G hfree (by omega) (by decide) hreg hcard c hc b⟩

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_sector_cases
