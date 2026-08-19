import Proofs.Erdos85EightEightMixedOwnerTerminalCapstone
import Proofs.Erdos85SizeTwoEigenlineEightEightTerminalAssembly
import Proofs.Erdos85SizeTwoEigenlineEightEightMixedExteriorModel

/-!
# Concrete mixed parameter-four terminal

This file connects the mixed shore case in the structural `8+8` terminal
assembly to the checked mixed-owner certificate.  Both orientations are
handled: the triangle-free shore is placed first before the fixed model is
constructed.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

/-- The mixed `r=4` structural socket is impossible whenever the standard
outside-pair feasibility data is available. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_mixed_parameterFour_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hVcard : Fintype.card V = 8 * 8)
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
    (hab4 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 4)
    (hba4 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 4)
    (haa3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3)
    (hbb3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 3)
    (hmixed :
      (EightEightShoreAllTf G c a ∧ EightEightShoreAllTriangle G c b) ∨
      (EightEightShoreAllTriangle G c a ∧ EightEightShoreAllTf G c b))
    (hpaircard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hpairinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (houtcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedgesNcard : (exteriorPairGraph G c).edgeSet.ncard = 48)
    : False := by
  letI : DecidablePred (· ∈ c.supp) :=
    fun x => (secondOrderDefectGraph G).instDecidableMemSupp c x
  have hRedges : (exteriorPairGraph G c).edgeFinset.card = 48 := by
    change (Set.toFinset (exteriorPairGraph G c).edgeSet).card = 48
    rw [← Set.ncard_eq_toFinset_card']
    exact hRedgesNcard
  have hflip : ∀ ⦃x y : c.supp⦄,
      (G.induce c.supp).Adj x y → s x.1 = -s y.1 := by
    intro x y hxy
    have hymem : y.1 ∈
        componentNeighborFinset G (secondOrderDefectGraph G) c x.1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset x.1 y.1).mpr hxy,
        (ConnectedComponent.mem_supp_iff c y.1).mp y.2⟩
    have hopen := (internal_alternation G hfree (by omega) hreg hVcard
      c hc s hs_in hs_out hA_in x.2).2 y.1 hymem
    linarith
  rcases hmixed with hforward | hreverse
  · obtain ⟨hleft, hright, hcross⟩ :=
      binarySquare_regular_sizeTwoPart_eight_eightEight_mixed_parameterFour_exteriorPair_model
        G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs a b hab
          u v huinj hvinj hurange hvrange hu hv hforward.1 hforward.2
          haa3 hbb3 hab4
    let label := eightEightCycleLabeling_of_shoreCoordinates
      G c hc a b hab u v huinj hvinj hurange hvrange hu hv
    let hmodel := mixedEight_intrinsicModel_of_shoreCoordinates
      G c hc a b hab u v huinj hvinj hurange hvrange hu hv s
        hleft hright hcross
    apply mixedEightExteriorPairModel_false_of_cycleLabeling
      G hfree c hpaircard hpairinc houtcard hRedges label s
        (fun x => hs_in x.1 x.2) hflip
    exact hmodel
  · obtain ⟨hleft, hright, hcross⟩ :=
      binarySquare_regular_sizeTwoPart_eight_eightEight_mixed_parameterFour_exteriorPair_model
        G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs b a hab.symm
          v u hvinj huinj hvrange hurange hv hu hreverse.2 hreverse.1
          hbb3 haa3 hba4
    let label := eightEightCycleLabeling_of_shoreCoordinates
      G c hc b a hab.symm v u hvinj huinj hvrange hurange hv hu
    let hmodel := mixedEight_intrinsicModel_of_shoreCoordinates
      G c hc b a hab.symm v u hvinj huinj hvrange hurange hv hu s
        hleft hright hcross
    apply mixedEightExteriorPairModel_false_of_cycleLabeling
      G hfree c hpaircard hpairinc houtcard hRedges label s
        (fun x => hs_in x.1 x.2) hflip
    exact hmodel

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_mixed_parameterFour_false
