import Proofs.Erdos85SizeTwoEigenlineAllTriangleFreeCycleDiagonal

/-!
# Exact sector trichotomy for the q=8 eight-plus-eight stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

For the quotient `[[7-r,r],[r,7-r]]`, the sharpened all-triangle upper
bound forces `r ≥ 4`, while the all-triangle-free lower bound forces
`r ≤ 5`.  Thus low parameters force both cycles all-triangle-free, high
parameters force both cycles all-triangle, and only `r=4,5` can remain mixed.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The q=8 `8+8` quotient parameter has three exhaustive sector regimes:
low (`r≤3`) is wholly triangle-free, middle is `r=4,5`, and high (`r≥6`)
is wholly all-triangle. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_sectorTrichotomy
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
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b) :
    ∃ r : ℕ, 2 ≤ r ∧ r ≤ 7 ∧
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
        (6 ≤ r ∧
          (∀ x : c.supp, x ∈ a.supp →
            (triangleFreeEdgeGraph G).degree x.1 = 0) ∧
          (∀ x : c.supp, x ∈ b.supp →
            (triangleFreeEdgeGraph G).degree x.1 = 0))) := by
  obtain ⟨r, hr2, hr7, haa, habq, hbaq, hbb, hsectorA, hsectorB⟩ :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_sectorRefinement
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb hab
  have htf_le (d : (G.induce c.supp).ConnectedComponent)
      (hdd : componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) d d = 7 - r)
      (htf : ∀ x : c.supp, x ∈ d.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 2) : r ≤ 5 :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangleFree_parameter_le_five
      G hfree hreg hcard c hc d r hdd htf
  have highSector (d : (G.induce c.supp).ConnectedComponent)
      (hdd : componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) d d = 7 - r)
      (hr6 : 6 ≤ r) :
      ∀ x : c.supp, x ∈ d.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 0 := by
    rcases binarySquare_regular_sizeTwoPart_internalCycle_sector_dichotomy
      G hfree (by omega) (by decide) hreg hcard c hc d with hall | htf
    · exact hall
    · have := htf_le d hdd htf
      omega
  have hregime :
      (r ≤ 3 ∧
          (∀ x : c.supp, x ∈ a.supp →
            (triangleFreeEdgeGraph G).degree x.1 = 2) ∧
          (∀ x : c.supp, x ∈ b.supp →
            (triangleFreeEdgeGraph G).degree x.1 = 2)) ∨
        (4 ≤ r ∧ r ≤ 5) ∨
        (6 ≤ r ∧
          (∀ x : c.supp, x ∈ a.supp →
            (triangleFreeEdgeGraph G).degree x.1 = 0) ∧
          (∀ x : c.supp, x ∈ b.supp →
            (triangleFreeEdgeGraph G).degree x.1 = 0)) := by
    by_cases hlow : r ≤ 3
    · left
      refine ⟨hlow, ?_, ?_⟩
      · rcases hsectorA with htf | hr4
        · exact htf
        · omega
      · rcases hsectorB with htf | hr4
        · exact htf
        · omega
    · by_cases hmid : r ≤ 5
      · exact Or.inr (Or.inl ⟨by omega, hmid⟩)
      · right; right
        have hr6 : 6 ≤ r := by omega
        exact ⟨hr6, highSector a haa hr6, highSector b hbb hr6⟩
  exact ⟨r, hr2, hr7, haa, habq, hbaq, hbb, hregime⟩

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_sectorTrichotomy
