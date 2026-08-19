import Proofs.Erdos85SizeTwoEigenlineEightEightSurvivingParameterEnumeration

/-!
# Exact shore-sector cases at parameter four

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The three checked parameter-four owner models correspond to: both shores
all-triangle-free, exactly one shore all-triangle-free, and both shores
all-triangle.  This theorem packages the two independent internal-cycle
sector dichotomies in precisely that terminal-facing form.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The two C8 shores fall into exactly the low, mixed, or both-triangle
sector case.  The mixed case retains its two possible orientations. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterFour_sectorCases
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
    (a b : (G.induce c.supp).ConnectedComponent) :
    ((∀ x : c.supp, x ∈ a.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 2) ∧
      (∀ x : c.supp, x ∈ b.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 2)) ∨
    (((∀ x : c.supp, x ∈ a.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 2) ∧
      (∀ x : c.supp, x ∈ b.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 0)) ∨
     ((∀ x : c.supp, x ∈ a.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 0) ∧
      (∀ x : c.supp, x ∈ b.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 2))) ∨
    ((∀ x : c.supp, x ∈ a.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 0) ∧
      (∀ x : c.supp, x ∈ b.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 0)) := by
  rcases binarySquare_regular_sizeTwoPart_internalCycle_sector_dichotomy
      G hfree (by omega) (by decide) hreg hcard c hc a with ha0 | ha2 <;>
    rcases binarySquare_regular_sizeTwoPart_internalCycle_sector_dichotomy
      G hfree (by omega) (by decide) hreg hcard c hc b with hb0 | hb2
  · exact Or.inr (Or.inr ⟨ha0, hb0⟩)
  · exact Or.inr (Or.inl (Or.inr ⟨ha0, hb2⟩))
  · exact Or.inr (Or.inl (Or.inl ⟨ha2, hb0⟩))
  · exact Or.inl ⟨ha2, hb2⟩

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameterFour_sectorCases
