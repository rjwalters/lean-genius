import Proofs.Erdos85EightEightLowOwnerTerminalCapstone
import Proofs.Erdos85EightEightMixedOwnerTerminalCapstone
import Proofs.Erdos85SizeTwoEigenlineEightEightTerminalAssembly
import Proofs.Erdos85SizeTwoEigenlineEightEightLowExteriorModel

/-!
# Concrete low parameter-four terminal

This file connects the all-triangle-free shore case in the structural
`8+8` assembly to the checked low-owner certificate.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

theorem lowZmodEightLeft_sameShore (i j : ZMod 8) :
    (zmodEightLeftFin16 i).val / 8 = (zmodEightLeftFin16 j).val / 8 := by
  revert i j
  decide

theorem lowZmodEightRight_sameShore (i j : ZMod 8) :
    (zmodEightRightFin16 i).val / 8 = (zmodEightRightFin16 j).val / 8 := by
  revert i j
  decide

theorem lowZmodEight_cross_not_sameShore (i j : ZMod 8) :
    (zmodEightLeftFin16 i).val / 8 ≠ (zmodEightRightFin16 j).val / 8 := by
  revert i j
  decide

/-- Exact shore coordinates assemble the low structural exterior relations
into the intrinsic conditional model used by phase alignment. -/
theorem lowEight_intrinsicModel_of_shoreCoordinates
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (s : V → ℤ)
    (hleft : ∀ i j : ZMod 8,
      (exteriorPairGraph G c.supp).Adj (u i) (u j) ↔
        j - i = 3 ∨ j - i = 5)
    (hright : ∀ i j : ZMod 8,
      (exteriorPairGraph G c.supp).Adj (v i) (v j) ↔
        j - i = 3 ∨ j - i = 5)
    (hcross : ∀ i j : ZMod 8,
      (exteriorPairGraph G c.supp).Adj (u i) (v j) ↔
        s (v j).1 ≠ s (u i).1) :
    let label := eightEightCycleLabeling_of_shoreCoordinates
      G c hc a b hab u v huinj hvinj hurange hvrange hu hv
    ∀ x y : c.supp,
      (exteriorPairGraph G c.supp).Adj x y ↔
        if (label.toEquiv x).val / 8 = (label.toEquiv y).val / 8 then
          eightEightLowExteriorPairGraph.Adj
            (label.toEquiv x) (label.toEquiv y)
        else s x.1 ≠ s y.1 := by
  dsimp only
  let label := eightEightCycleLabeling_of_shoreCoordinates
    G c hc a b hab u v huinj hvinj hurange hvrange hu hv
  let coord := eightEightShoreCoordinateEquiv
    G c hc a b hab u v huinj hvinj hurange hvrange
  have hlabelu (i : ZMod 8) :
      label.toEquiv (u i) = zmodEightLeftFin16 i := by
    change coord (u i) = zmodEightLeftFin16 i
    exact eightEightShoreCoordinateEquiv_apply_u
      G c hc a b hab u v huinj hvinj hurange hvrange i
  have hlabelv (j : ZMod 8) :
      label.toEquiv (v j) = zmodEightRightFin16 j := by
    change coord (v j) = zmodEightRightFin16 j
    exact eightEightShoreCoordinateEquiv_apply_v
      G c hc a b hab u v huinj hvinj hurange hvrange j
  have hcover := eightEight_shores_cover
    G c hc a b hab u v huinj hvinj hurange hvrange
  intro x y
  rcases hcover x with hxa | hxb <;>
    rcases hcover y with hya | hyb
  · rw [← hurange] at hxa hya
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, rfl⟩ := hya
    rw [hlabelu, hlabelu, if_pos (lowZmodEightLeft_sameShore i j),
      hleft, eightEightLowExteriorPairGraph_left]
  · rw [← hurange] at hxa
    rw [← hvrange] at hyb
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, rfl⟩ := hyb
    rw [hlabelu, hlabelv, if_neg (lowZmodEight_cross_not_sameShore i j), hcross]
    exact ne_comm
  · rw [← hvrange] at hxb
    rw [← hurange] at hya
    obtain ⟨j, rfl⟩ := hxb
    obtain ⟨i, rfl⟩ := hya
    rw [hlabelv, hlabelu,
      if_neg (ne_comm.mp (lowZmodEight_cross_not_sameShore i j)),
      (exteriorPairGraph G c.supp).adj_comm, hcross]
  · rw [← hvrange] at hxb hyb
    obtain ⟨i, rfl⟩ := hxb
    obtain ⟨j, rfl⟩ := hyb
    rw [hlabelv, hlabelv, if_pos (lowZmodEightRight_sameShore i j),
      hright, eightEightLowExteriorPairGraph_right]

/-- The low `r=4` structural socket is impossible whenever the standard
outside-pair feasibility data is available. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_low_parameterFour_false
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
    (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (haa3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3)
    (hab4 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 4)
    (_hba4 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 4)
    (hbb3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 3)
    (htfA : EightEightShoreAllTf G c a)
    (htfB : EightEightShoreAllTf G c b)
    (hpaircard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hpairinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (houtcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedgesNcard : (exteriorPairGraph G c).edgeSet.ncard = 48) :
    False := by
  letI : DecidablePred (· ∈ c.supp) :=
    fun x => (secondOrderDefectGraph G).instDecidableMemSupp c x
  have hRedges : (exteriorPairGraph G c).edgeFinset.card = 48 := by
    change (Set.toFinset (exteriorPairGraph G c).edgeSet).card = 48
    rw [← Set.ncard_eq_toFinset_card']
    exact hRedgesNcard
  obtain ⟨hleft, hright, hcross⟩ :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangleFree_parameterFour_exteriorPair_model
      G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs a b hab
        u v huinj hvinj hurange hvrange hu hv htfA htfB haa3 hbb3 hab4
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
  let label := eightEightCycleLabeling_of_shoreCoordinates
    G c hc a b hab u v huinj hvinj hurange hvrange hu hv
  apply lowEightExteriorPairModel_false_of_cycleLabeling
    G hfree c hpaircard hpairinc houtcard hRedges label s
      (fun x => hs_in x.1 x.2) hflip
  exact lowEight_intrinsicModel_of_shoreCoordinates
    G c hc a b hab u v huinj hvinj hurange hvrange hu hv s
      hleft hright hcross

end

end Erdos85

#print axioms Erdos85.lowEight_intrinsicModel_of_shoreCoordinates
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_low_parameterFour_false
