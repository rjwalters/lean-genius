import Proofs.Erdos85EightEightMixedExteriorModelCapstone
import Proofs.Erdos85EightEightCoordinateCover

/-!
# Concrete mixed eight-plus-eight owner terminal

This file turns the two cyclic shore maps emitted by the structural r=4
analysis into the intrinsic cycle labeling consumed by the checked mixed
owner certificate.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

theorem eightEightCycleGraph_left_zmod (i j : ZMod 8) :
    eightEightCycleGraph.Adj
        (zmodEightLeftFin16 i)
        (zmodEightLeftFin16 j) ↔
      j = i - 1 ∨ j = i + 1 := by
  revert i j
  decide

theorem eightEightCycleGraph_right_zmod (i j : ZMod 8) :
    eightEightCycleGraph.Adj
        (zmodEightRightFin16 i)
        (zmodEightRightFin16 j) ↔
      j = i - 1 ∨ j = i + 1 := by
  revert i j
  decide

theorem eightEightCycleGraph_cross_zmod (i j : ZMod 8) :
    ¬ eightEightCycleGraph.Adj
        (zmodEightLeftFin16 i)
        (zmodEightRightFin16 j) := by
  revert i j
  decide

theorem mixedZmodEightLeft_sameShore (i j : ZMod 8) :
    (MixedOwnerBridge.zmodEightLeftFin16 i).val / 8 =
      (MixedOwnerBridge.zmodEightLeftFin16 j).val / 8 := by
  revert i j
  decide

theorem mixedZmodEightRight_sameShore (i j : ZMod 8) :
    (MixedOwnerBridge.zmodEightRightFin16 i).val / 8 =
      (MixedOwnerBridge.zmodEightRightFin16 j).val / 8 := by
  revert i j
  decide

theorem mixedZmodEight_cross_not_sameShore (i j : ZMod 8) :
    (MixedOwnerBridge.zmodEightLeftFin16 i).val / 8 ≠
      (MixedOwnerBridge.zmodEightRightFin16 j).val / 8 := by
  revert i j
  decide

/-- The exact shore coordinates canonically label the internal graph as two
disjoint fixed eight-cycles. -/
noncomputable def eightEightCycleLabeling_of_shoreCoordinates
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
  let coord := eightEightShoreCoordinateEquiv
    G c hc a b hab u v huinj hvinj hurange hvrange
  have hcover := eightEight_shores_cover
    G c hc a b hab u v huinj hvinj hurange hvrange
  refine ⟨coord, ?_⟩
  intro x y
  rcases hcover x with hxa | hxb <;>
    rcases hcover y with hya | hyb
  · rw [← hurange] at hxa hya
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, rfl⟩ := hya
    rw [eightEightShoreCoordinateEquiv_apply_u,
      eightEightShoreCoordinateEquiv_apply_u,
      eightEightCycleGraph_left_zmod]
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
      exact (eightEightCycleGraph_cross_zmod i j (by
        simpa [coord] using hfixed)).elim
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
      exact (eightEightCycleGraph_cross_zmod j i (by
        simpa [coord] using hfixed.symm)).elim
  · rw [← hvrange] at hxb hyb
    obtain ⟨i, rfl⟩ := hxb
    obtain ⟨j, rfl⟩ := hyb
    rw [eightEightShoreCoordinateEquiv_apply_v,
      eightEightShoreCoordinateEquiv_apply_v,
      eightEightCycleGraph_right_zmod]
    rw [← H.mem_neighborFinset, hv]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl (hvinj h)
      · exact Or.inr (hvinj h)
    · rintro (rfl | rfl) <;> simp

/-- The three shore-wise relations of the structural mixed model assemble
into the intrinsic conditional form expected by phase alignment. -/
theorem mixedEight_intrinsicModel_of_shoreCoordinates
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
        j - i = 1 ∨ j - i = 7)
    (hcross : ∀ i j : ZMod 8,
      (exteriorPairGraph G c.supp).Adj (u i) (v j) ↔
        s (v j).1 ≠ s (u i).1) :
    let label := eightEightCycleLabeling_of_shoreCoordinates
      G c hc a b hab u v huinj hvinj hurange hvrange hu hv
    ∀ x y : c.supp,
      (exteriorPairGraph G c.supp).Adj x y ↔
        if (label.toEquiv x).val / 8 = (label.toEquiv y).val / 8 then
          MixedOwnerBridge.eightEightMixedExteriorPairGraph.Adj
            (label.toEquiv x) (label.toEquiv y)
        else s x.1 ≠ s y.1 := by
  dsimp only
  let label := eightEightCycleLabeling_of_shoreCoordinates
    G c hc a b hab u v huinj hvinj hurange hvrange hu hv
  let coord := eightEightShoreCoordinateEquiv
    G c hc a b hab u v huinj hvinj hurange hvrange
  have hlabelu (i : ZMod 8) :
      label.toEquiv (u i) = MixedOwnerBridge.zmodEightLeftFin16 i := by
    change coord (u i) = MixedOwnerBridge.zmodEightLeftFin16 i
    rw [show MixedOwnerBridge.zmodEightLeftFin16 i = zmodEightLeftFin16 i by rfl]
    exact eightEightShoreCoordinateEquiv_apply_u
      G c hc a b hab u v huinj hvinj hurange hvrange i
  have hlabelv (j : ZMod 8) :
      label.toEquiv (v j) = MixedOwnerBridge.zmodEightRightFin16 j := by
    change coord (v j) = MixedOwnerBridge.zmodEightRightFin16 j
    rw [show MixedOwnerBridge.zmodEightRightFin16 j = zmodEightRightFin16 j by rfl]
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
    rw [hlabelu, hlabelu, if_pos (mixedZmodEightLeft_sameShore i j),
      hleft, MixedOwnerBridge.eightEightMixedExteriorPairGraph_left]
  · rw [← hurange] at hxa
    rw [← hvrange] at hyb
    obtain ⟨i, rfl⟩ := hxa
    obtain ⟨j, rfl⟩ := hyb
    rw [hlabelu, hlabelv, if_neg (mixedZmodEight_cross_not_sameShore i j), hcross]
    exact ne_comm
  · rw [← hvrange] at hxb
    rw [← hurange] at hya
    obtain ⟨j, rfl⟩ := hxb
    obtain ⟨i, rfl⟩ := hya
    rw [hlabelv, hlabelu, if_neg (ne_comm.mp (mixedZmodEight_cross_not_sameShore i j)),
      (exteriorPairGraph G c.supp).adj_comm,
      hcross]
  · rw [← hvrange] at hxb hyb
    obtain ⟨i, rfl⟩ := hxb
    obtain ⟨j, rfl⟩ := hyb
    rw [hlabelv, hlabelv, if_pos (mixedZmodEightRight_sameShore i j),
      hright, MixedOwnerBridge.eightEightMixedExteriorPairGraph_right]
end

end Erdos85

#print axioms Erdos85.eightEightCycleLabeling_of_shoreCoordinates
#print axioms Erdos85.mixedEight_intrinsicModel_of_shoreCoordinates
