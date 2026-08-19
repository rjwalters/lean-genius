import Proofs.Erdos85EightEightBothTriangleOwnerTerminalCapstone
import Proofs.Erdos85EightEightBothTriangleCoordinateCover
import Proofs.Erdos85SizeTwoEigenlineEightEightBothTriangleExteriorModel

/-!
# Concrete both-triangle parameter-four terminal

This file connects the both-all-triangle shore case in the structural `8+8`
terminal assembly to the checked both-triangle owner certificate.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

open BothTriangleOwnerBridge

private theorem bothCycleGraph_left (i j : ZMod 8) :
    eightEightCycleGraph.Adj (zmodEightLeftFin16 i) (zmodEightLeftFin16 j) ↔
      j = i - 1 ∨ j = i + 1 := by
  revert i j
  decide

private theorem bothCycleGraph_right (i j : ZMod 8) :
    eightEightCycleGraph.Adj (zmodEightRightFin16 i) (zmodEightRightFin16 j) ↔
      j = i - 1 ∨ j = i + 1 := by
  revert i j
  decide

private theorem bothCycleGraph_cross (i j : ZMod 8) :
    ¬ eightEightCycleGraph.Adj (zmodEightLeftFin16 i) (zmodEightRightFin16 j) := by
  revert i j
  decide

private theorem bothLeft_sameShore (i j : ZMod 8) :
    (zmodEightLeftFin16 i).val / 8 = (zmodEightLeftFin16 j).val / 8 := by
  revert i j
  decide

private theorem bothRight_sameShore (i j : ZMod 8) :
    (zmodEightRightFin16 i).val / 8 = (zmodEightRightFin16 j).val / 8 := by
  revert i j
  decide

private theorem bothCross_not_sameShore (i j : ZMod 8) :
    (zmodEightLeftFin16 i).val / 8 ≠ (zmodEightRightFin16 j).val / 8 := by
  revert i j
  decide

/-- The exact cyclic shore coordinates label the internal graph by the fixed
disjoint union of two eight-cycles. -/
noncomputable def bothTriangleCycleLabeling_of_shoreCoordinates
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
      {v (z - 1), v (z + 1)}) :
    EightEightCycleLabeling (G.induce c.supp) := by
  let H := G.induce c.supp
  let coord := bothTriangleEightShoreCoordinateEquiv
    G c hc a b hab u v huinj hvinj hurange hvrange
  have hcover := bothTriangleEight_shores_cover
    G c hc a b hab u v huinj hvinj hurange hvrange
  refine ⟨coord, ?_⟩
  intro x y
  rcases hcover x with hxa | hxb <;> rcases hcover y with hya | hyb
  · rw [← hurange] at hxa hya
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, rfl⟩ := hya
    rw [bothTriangleEightShoreCoordinateEquiv_apply_u,
      bothTriangleEightShoreCoordinateEquiv_apply_u, bothCycleGraph_left]
    rw [← H.mem_neighborFinset, hu]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl (huinj h)
      · exact Or.inr (huinj h)
    · rintro (rfl | rfl) <;> simp
  · rw [← hurange] at hxa
    rw [← hvrange] at hyb
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, rfl⟩ := hyb
    constructor
    · intro huv
      have hvA : v j ∈ a.supp :=
        (ConnectedComponent.mem_supp_congr_adj a huv).mp (by
          rw [← hurange]; exact ⟨i, rfl⟩)
      exact (hab (ConnectedComponent.eq_of_common_vertex hvA (by
        rw [← hvrange]; exact ⟨j, rfl⟩))).elim
    · intro hfixed
      exact (bothCycleGraph_cross i j (by simpa [coord] using hfixed)).elim
  · rw [← hvrange] at hxb
    rw [← hurange] at hya
    obtain ⟨i, rfl⟩ := hxb
    obtain ⟨j, rfl⟩ := hya
    constructor
    · intro hvu
      have huB : u j ∈ b.supp :=
        (ConnectedComponent.mem_supp_congr_adj b hvu).mp (by
          rw [← hvrange]; exact ⟨i, rfl⟩)
      exact (hab (ConnectedComponent.eq_of_common_vertex (by
        rw [← hurange]; exact ⟨j, rfl⟩) huB)).elim
    · intro hfixed
      exact (bothCycleGraph_cross j i (by
        simpa [coord] using hfixed.symm)).elim
  · rw [← hvrange] at hxb hyb
    obtain ⟨i, rfl⟩ := hxb
    obtain ⟨j, rfl⟩ := hyb
    rw [bothTriangleEightShoreCoordinateEquiv_apply_v,
      bothTriangleEightShoreCoordinateEquiv_apply_v, bothCycleGraph_right]
    rw [← H.mem_neighborFinset, hv]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl (hvinj h)
      · exact Or.inr (hvinj h)
    · rintro (rfl | rfl) <;> simp

/-- The two shore-wise offset-`±1` laws and the cross-shore sign law assemble
into the intrinsic conditional model consumed by phase alignment. -/
theorem bothTriangleEight_intrinsicModel_of_shoreCoordinates
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
        j - i = 1 ∨ j - i = 7)
    (hright : ∀ i j : ZMod 8,
      (exteriorPairGraph G c.supp).Adj (v i) (v j) ↔
        j - i = 1 ∨ j - i = 7)
    (hcross : ∀ i j : ZMod 8,
      (exteriorPairGraph G c.supp).Adj (u i) (v j) ↔
        s (v j).1 ≠ s (u i).1) :
    let label := bothTriangleCycleLabeling_of_shoreCoordinates
      G c hc a b hab u v huinj hvinj hurange hvrange hu hv
    ∀ x y : c.supp,
      (exteriorPairGraph G c.supp).Adj x y ↔
        if (label.toEquiv x).val / 8 = (label.toEquiv y).val / 8 then
          eightEightBothTriangleExteriorPairGraph.Adj
            (label.toEquiv x) (label.toEquiv y)
        else s x.1 ≠ s y.1 := by
  dsimp only
  let label := bothTriangleCycleLabeling_of_shoreCoordinates
    G c hc a b hab u v huinj hvinj hurange hvrange hu hv
  let coord := bothTriangleEightShoreCoordinateEquiv
    G c hc a b hab u v huinj hvinj hurange hvrange
  have hlabelu (i : ZMod 8) :
      label.toEquiv (u i) = zmodEightLeftFin16 i := by
    change coord (u i) = zmodEightLeftFin16 i
    exact bothTriangleEightShoreCoordinateEquiv_apply_u
      G c hc a b hab u v huinj hvinj hurange hvrange i
  have hlabelv (j : ZMod 8) :
      label.toEquiv (v j) = zmodEightRightFin16 j := by
    change coord (v j) = zmodEightRightFin16 j
    exact bothTriangleEightShoreCoordinateEquiv_apply_v
      G c hc a b hab u v huinj hvinj hurange hvrange j
  have hcover := bothTriangleEight_shores_cover
    G c hc a b hab u v huinj hvinj hurange hvrange
  intro x y
  rcases hcover x with hxa | hxb <;>
    rcases hcover y with hya | hyb
  · rw [← hurange] at hxa hya
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, rfl⟩ := hya
    rw [hlabelu, hlabelu, if_pos (bothLeft_sameShore i j),
      hleft, eightEightBothTriangleExteriorPairGraph_left]
  · rw [← hurange] at hxa
    rw [← hvrange] at hyb
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, rfl⟩ := hyb
    rw [hlabelu, hlabelv, if_neg (bothCross_not_sameShore i j), hcross]
    exact ne_comm
  · rw [← hvrange] at hxb
    rw [← hurange] at hya
    obtain ⟨j, rfl⟩ := hxb
    obtain ⟨i, rfl⟩ := hya
    rw [hlabelv, hlabelu,
      if_neg (ne_comm.mp (bothCross_not_sameShore i j)),
      (exteriorPairGraph G c.supp).adj_comm, hcross]
  · rw [← hvrange] at hxb hyb
    obtain ⟨i, rfl⟩ := hxb
    obtain ⟨j, rfl⟩ := hyb
    rw [hlabelv, hlabelv, if_pos (bothRight_sameShore i j),
      hright, eightEightBothTriangleExteriorPairGraph_right]

/-- The both-all-triangle `r=4` structural socket contradicts the checked
owner certificate whenever the standard outside-pair feasibility data is
available. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_bothTriangle_parameterFour_false
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
    (hallA : ∀ x : c.supp, x ∈ a.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 0)
    (hallB : ∀ x : c.supp, x ∈ b.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 0)
    (haa3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3)
    (hbb3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 3)
    (hab4 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 4)
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
  obtain ⟨hleft, hright, hcross⟩ :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_bothTriangle_parameterFour_exteriorPair_model
      G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs a b hab
        u v huinj hvinj hurange hvrange hu hv hallA hallB haa3 hbb3 hab4
  let label := bothTriangleCycleLabeling_of_shoreCoordinates
    G c hc a b hab u v huinj hvinj hurange hvrange hu hv
  let hmodel := bothTriangleEight_intrinsicModel_of_shoreCoordinates
    G c hc a b hab u v huinj hvinj hurange hvrange hu hv s
      hleft hright hcross
  apply bothTriangleEightExteriorPairModel_false_of_cycleLabeling
    G hfree c hpaircard hpairinc houtcard hRedges label s
      (fun x => hs_in x.1 x.2) hflip
  exact hmodel

end

end Erdos85

#print axioms Erdos85.bothTriangleEight_intrinsicModel_of_shoreCoordinates
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_bothTriangle_parameterFour_false
