import Proofs.Erdos85EightEightHighConcreteModel
import Proofs.Erdos85EightEightHighOwnerOutsideTransport

/-! # Concrete terminal for the high eight-plus-eight branch -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

/-- The quotient-six high branch is contradictory after normalizing the two
signed eight-cycle shores and applying the checked high-owner certificate. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_high_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hVcard : Fintype.card V = 8 * 8)
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
    (hab6 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 6)
    (hba6 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 6)
    (hpaircard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hpairinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (houtcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedgesNcard : (exteriorPairGraph G c).edgeSet.ncard = 48) : False := by
  letI hmem : DecidablePred (· ∈ (c : Set V)) :=
    fun x => (secondOrderDefectGraph G).instDecidableMemSupp c x
  have hRedges : (exteriorPairGraph G c).edgeFinset.card = 48 := by
    change (Set.toFinset (exteriorPairGraph G c).edgeSet).card = 48
    rw [← Set.ncard_eq_toFinset_card']
    exact hRedgesNcard
  classical
  let H := G.induce c.supp
  have hHdeg : ∀ x : c.supp, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hVcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) x
  have hflip : ∀ ⦃x y : c.supp⦄, H.Adj x y → s x.1 = -s y.1 := by
    intro x y hxy
    have hymem : y.1 ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c x.1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hxy, y.2⟩
    have hyx := (internal_alternation G hfree (by omega) hreg hVcard c hc s
      hs_in hs_out hA_in x.2).2 y.1 hymem
    omega
  have hsignA : ∀ x ∈ a.supp,
      s x.1 = -1 ∨ s x.1 = 1 := by
    intro x _hx
    exact hs_in x.1 x.2
  have hsignB : ∀ x ∈ b.supp,
      s x.1 = -1 ∨ s x.1 = 1 := by
    intro x _hx
    exact hs_in x.1 x.2
  obtain ⟨nu⟩ := exists_normalizedEightShoreCoordinates
    H hHdeg a ha (fun x => s x.1) hsignA hflip
  obtain ⟨nv⟩ := exists_normalizedEightShoreCoordinates
    H hHdeg b hb (fun x => s x.1) hsignB hflip
  let u := nu.u
  let v := nv.u
  let R := eightEightHighCoordinateExteriorGraph G c (by omega)
    a b hab u v nu.injective nv.injective nu.range nv.range
  letI : DecidableRel R.Adj := Classical.decRel R.Adj
  have hsupport := eightEightHighCoordinateExteriorGraph_fixed_and_candidate
    G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
      u v nu.injective nv.injective nu.range nv.range nu.neighbor nv.neighbor
      nu.sign nv.sign hab6 hba6
  let modelIso : exteriorPairGraph G c ≃g R :=
    (connectedComponentExteriorSuppIso G c).trans
      (eightEightHighCoordinateExteriorGraphIso G c (by omega)
        a b hab u v nu.injective nv.injective nu.range nv.range)
  have hcycle : ∀ x y : c.supp, G.Adj x.1 y.1 ↔
      eightEightHighCycleAdj (modelIso x).val (modelIso y).val = true := by
    intro x y
    simpa [modelIso, connectedComponentExteriorSuppIso,
      connectedComponentSupportEquiv] using
      eightEightHighCoordinateExteriorGraphIso_cycle G c (by omega)
        a b hab u v nu.injective nv.injective nu.range nv.range
          nu.neighbor nv.neighbor x y
  apply highEightOwnerModel_false_of_cross_laws G hfree c hpaircard hpairinc
    houtcard hRedges R hsupport.1 hsupport.2 modelIso hcycle
  · dsimp only
    let active := eightEightHighCoordinateActive R
    let out := highOwnerOutsideEquiv G c hpaircard hpairinc houtcard hRedges R
      hsupport.1 hsupport.2 modelIso
    let X := eightEightHighRealizedRelation active (G.induce c.suppᶜ) out
    have hlaws := eightEightHighCoordinateExteriorGraph_cross_laws
      G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
        u v nu.injective nv.injective nu.range nv.range nu.neighbor nv.neighbor
          nu.sign nv.sign hab6 X
    simpa [active, X, eightEightHighOwnerClassicalVal,
      eightEightHighCoordinateClassicalVal] using hlaws.1
  · dsimp only
    let active := eightEightHighCoordinateActive R
    let out := highOwnerOutsideEquiv G c hpaircard hpairinc houtcard hRedges R
      hsupport.1 hsupport.2 modelIso
    let X := eightEightHighRealizedRelation active (G.induce c.suppᶜ) out
    have hlaws := eightEightHighCoordinateExteriorGraph_cross_laws
      G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
        u v nu.injective nv.injective nu.range nv.range nu.neighbor nv.neighbor
          nu.sign nv.sign hab6 X
    simpa [active, X, eightEightHighOwnerClassicalVal,
      eightEightHighCoordinateClassicalVal] using hlaws.2

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_high_false
