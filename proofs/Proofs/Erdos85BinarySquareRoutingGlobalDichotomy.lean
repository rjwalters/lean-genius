import Proofs.Erdos85BinarySquareRoutingMultiplicityDichotomy

/-! # Component-wide routing multiplicity dichotomy -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For fixed endpoint, intermediate, and routing components, either the
routing component contains the corresponding owner-color rainbow triangle,
or every directly colored endpoint pair has exactly its two canonical star
completions through the intermediate component. -/
theorem binarySquare_regular_sizeTwoRoutingColor_rainbow_or_all_two_lifts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (he : e.supp.ncard = q * 2) :
    (∃ y₁ y₂ y₃ : d.supp,
      y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₁ ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) e).Adj y₁.1 y₂.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj y₂.1 y₃.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj y₃.1 y₁.1) ∨
    (∀ (x : c.supp) (w : f.supp),
      d = crossIntermediateComponent G hfree hcf x w →
      ((Finset.univ : Finset e.supp).filter fun z =>
        d = crossIntermediateComponent G hfree hce x z ∧
          d = crossIntermediateComponent G hfree hef z w).card = 2) := by
  classical
  by_cases hrainbow : ∃ y₁ y₂ y₃ : d.supp,
      y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₁ ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) e).Adj y₁.1 y₂.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj y₂.1 y₃.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj y₃.1 y₁.1
  · exact Or.inl hrainbow
  · right
    intro x w hroute
    rcases binarySquare_regular_sizeTwoRoutingColor_two_lifts_or_owner_rainbow
      G hfree hq hreg hcard c d e f hce hef hcf he x w hroute with htwo | hr
    · exact htwo
    · exact False.elim (hrainbow hr)

end

end Erdos85
