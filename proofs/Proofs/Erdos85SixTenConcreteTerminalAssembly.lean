import Proofs.Erdos85SizeTwoEigenlineSixTenTerminalAssembly
import Proofs.Erdos85SizeTwoEigenlineSixTenMixedExteriorModel
import Proofs.Erdos85SizeTwoEigenlineSixTenAllTfExteriorModel
import Proofs.Erdos85SixTenOwnerStructuralTerminal

/-!
# Concrete terminal assembly for the `6+10` stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

This file connects the graph-theoretic exterior-pair classifications to the
two checked owner certificates.  The only remaining coordinate input is the
standard sign-normalized cyclic parametrization of the two shores.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A sign-normalized `C6 ⊔ C10` realization is impossible.  Both possible
triangle-free sectors are discharged internally by their checked owner
certificates. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_false_of_normalized_coordinates
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
    (hab : a ≠ b) (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hsu : ∀ i, s (u i).1 =
      sixTenParitySign ((ZMod.finEquiv 6).symm i).val)
    (hsv : ∀ j, s (v j).1 =
      sixTenParitySign ((ZMod.finEquiv 10).symm j).val)
    (hpaircard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hpairinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (houtcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedgesNcard : (exteriorPairGraph G c).edgeSet.ncard = 48) : False := by
  letI : DecidablePred (· ∈ c.supp) :=
    fun x => (secondOrderDefectGraph G).instDecidableMemSupp c x
  have hRedges : (exteriorPairGraph G c).edgeFinset.card = 48 := by
    change (Set.toFinset (exteriorPairGraph G c).edgeSet).card = 48
    rw [← Set.ncard_eq_toFinset_card']
    exact hRedgesNcard
  apply binarySquare_regular_sizeTwoPart_eight_sixTen_false_of_terminals
    G hfree hreg hVcard c hc s hs_in hs_out hA_in a b ha hb
  · intro _hshort hball
    obtain ⟨hleft, hright, hcross⟩ :=
      binarySquare_regular_sizeTwoPart_eight_sixTen_mixed_exteriorPair_model
        G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs a b ha hb
          hball u v huinj hvinj hurange hvrange hu hv
    exact sixTenMixedExteriorPairModel_false_of_normalized_shores
      G hfree c hpaircard hpairinc houtcard hRedges hc a b hab
        u v huinj hvinj hurange hvrange hu hv s hsu hsv hleft hright hcross
  · intro _hshort hbtf
    obtain ⟨hleft, hright, hcross⟩ :=
      binarySquare_regular_sizeTwoPart_eight_sixTen_allTf_exteriorPair_model
        G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs a b ha hb
          hbtf u v huinj hvinj hurange hvrange hu hv
    exact sixTenAllTfExteriorPairModel_false_of_normalized_shores
      G hfree c hpaircard hpairinc houtcard hRedges hc a b hab
        u v huinj hvinj hurange hvrange hu hv s hsu hsv hleft hright hcross

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_false_of_normalized_coordinates
