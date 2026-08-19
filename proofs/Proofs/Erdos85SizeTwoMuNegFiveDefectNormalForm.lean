import Proofs.Erdos85SizeTwoMuNegFiveMatchingNormalization
import Proofs.Erdos85SizeTwoMuNegFiveNeutralDefectComplement

/-! # Full signed defect normal form at `mu=-5` -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The defect graph induced on the signed sixteen-component consists of a
free perfect matching on each shore and, across the shores, the complement
of the neutral-projection two-factor. -/
theorem orderSixtyFour_sizeTwo_muNegFive_signed_defect_normalForm
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
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-5 : ℤ) * s z) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegFivePositiveShore D c s
    let Xm := MuNegFiveNegativeShore D c s
    let N := MuNegFiveNeutralProjection G c s
    ∃ fp : Equiv.Perm Xp, ∃ fm : Equiv.Perm Xm,
      (∀ x, fp (fp x) = x) ∧ (∀ x, fp x ≠ x) ∧
      (∀ y, fm (fm y) = y) ∧ (∀ y, fm y ≠ y) ∧
      (∀ x x', D.Adj x.1 x'.1 ↔ fp x = x') ∧
      (∀ y y', D.Adj y.1 y'.1 ↔ fm y = y') ∧
      ∀ x y, D.Adj x.1 y.1 ↔ ¬ N x y := by
  classical
  dsimp only
  obtain ⟨fp, fm, hfp, hfpinv, hfpne, hfm, hfminv, hfmne⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_sameSign_defect_matchings
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hcross :=
    orderSixtyFour_sizeTwo_muNegFive_neutralProjection_iff_not_defect
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  refine ⟨fp, fm, hfpinv, hfpne, hfminv, hfmne, hfp, hfm, ?_⟩
  intro x y
  constructor
  · intro hDxy hNxy
    exact (hcross x y).1 hNxy hDxy
  · intro hnotN
    by_contra hnotD
    exact hnotN ((hcross x y).2 hnotD)

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_signed_defect_normalForm
