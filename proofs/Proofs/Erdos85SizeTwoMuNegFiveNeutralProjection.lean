import Proofs.Erdos85SizeTwoMuNegFiveNeutralIncidence
import Proofs.Erdos85BiregularSubdivisionProjection

/-! # The neutral fiber projects to a biregular shore relation at `mu=-5` -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The shore relation witnessed by a neutral exterior vertex. -/
abbrev MuNegFiveNeutralProjection
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent) (s : V → ℤ) :
    MuNegFivePositiveShore (secondOrderDefectGraph G) c s →
      MuNegFiveNegativeShore (secondOrderDefectGraph G) c s → Prop :=
  subdivisionProjection
    (fun x => fun z : MuNegFiveNeutralFiber G c s => G.Adj x.1 z.1)
    (fun y => fun z : MuNegFiveNeutralFiber G c s => G.Adj y.1 z.1)

/-- Suppressing the neutral exterior vertices produces a two-biregular
relation between the positive and negative component shores. -/
theorem orderSixtyFour_sizeTwo_muNegFive_neutralProjection_biregular
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
    let S0 := MuNegFiveNeutralFiber G c s
    let R0p := fun x : Xp => fun z : S0 => G.Adj x.1 z.1
    let R0m := fun y : Xm => fun z : S0 => G.Adj y.1 z.1
    let N := MuNegFiveNeutralProjection G c s
    (∀ x, ((Finset.univ : Finset Xm).filter fun y => N x y).card = 2) ∧
    ∀ y, ((Finset.univ : Finset Xp).filter fun x => N x y).card = 2 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  let S0 := MuNegFiveNeutralFiber G c s
  let R0p := fun x : Xp => fun z : S0 => G.Adj x.1 z.1
  let R0m := fun y : Xm => fun z : S0 => G.Adj y.1 z.1
  have hneutral := orderSixtyFour_sizeTwo_muNegFive_neutralIncidence_biregular
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hpair : ∀ ⦃x : Xp⦄ ⦃y : Xm⦄ ⦃z w : S0⦄,
      R0p x z → R0m y z → R0p x w → R0m y w → z = w := by
    intro x y z w hxz hyz hxw hyw
    apply Subtype.ext
    have hxy : x.1 ≠ y.1 := by
      intro h
      have hsxy := congrArg s h
      rw [x.2.2, y.2.2] at hsxy
      omega
    apply Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree x.1 y.1 hxy)
    · exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hxz,
        (G.mem_neighborFinset _ _).mpr hyz⟩
    · exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset _ _).mpr hxw,
        (G.mem_neighborFinset _ _).mpr hyw⟩
  exact subdivisionProjection_biregular R0p R0m 2
    hneutral.1 hneutral.2.2.1 hneutral.2.1 hneutral.2.2.2 hpair

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_neutralProjection_biregular
