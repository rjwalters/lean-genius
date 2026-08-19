import Proofs.Erdos85EightEightCoordinateCover
import Proofs.Erdos85EightEightLowExteriorModelIso

/-! # Sign-aligned coordinates for two cyclic eight-shores -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

theorem eightEightCycleGraph_zmodLeft_iff (i j : ZMod 8) :
    eightEightCycleGraph.Adj (zmodEightLeftFin16 i)
      (zmodEightLeftFin16 j) ↔ j = i - 1 ∨ j = i + 1 := by
  revert i j
  native_decide

theorem eightEightCycleGraph_zmodRight_iff (i j : ZMod 8) :
    eightEightCycleGraph.Adj (zmodEightRightFin16 i)
      (zmodEightRightFin16 j) ↔ j = i - 1 ∨ j = i + 1 := by
  revert i j
  native_decide

theorem eightEightCycleGraph_zmod_cross (i j : ZMod 8) :
    ¬eightEightCycleGraph.Adj (zmodEightLeftFin16 i)
      (zmodEightRightFin16 j) := by
  revert i j
  native_decide

/-- The explicit two-shore coordinate equivalence is also a labeling by
the fixed disjoint union of two eight-cycles. -/
def eightEightCycleLabeling_of_shoreCoordinates
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
    EightEightCycleLabeling (G.induce c.supp) where
  toEquiv := eightEightShoreCoordinateEquiv G c hc a b hab u v
    huinj hvinj hurange hvrange
  map_adj_iff := by
    let H := G.induce c.supp
    intro x y
    have hcover := eightEight_shores_cover G c hc a b hab u v
      huinj hvinj hurange hvrange
    rcases hcover x with hxa | hxb <;>
      rcases hcover y with hya | hyb
    · rw [← hurange] at hxa hya
      obtain ⟨i, rfl⟩ := hxa
      obtain ⟨j, rfl⟩ := hya
      rw [← H.mem_neighborFinset, hu]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rw [huinj.eq_iff, huinj.eq_iff]
      simpa only [eightEightShoreCoordinateEquiv_apply_u] using
        (eightEightCycleGraph_zmodLeft_iff i j).symm
    · rw [← hurange] at hxa
      rw [← hvrange] at hyb
      obtain ⟨i, rfl⟩ := hxa
      obtain ⟨j, rfl⟩ := hyb
      have hnot : ¬H.Adj (u i) (v j) := by
        intro hadj
        apply hab
        have hui : H.connectedComponentMk (u i) = a :=
          (ConnectedComponent.mem_supp_iff a _).mp (by
            rw [← hurange]; exact ⟨i, rfl⟩)
        have hvj : H.connectedComponentMk (v j) = b :=
          (ConnectedComponent.mem_supp_iff b _).mp (by
            rw [← hvrange]; exact ⟨j, rfl⟩)
        exact hui.symm.trans
          ((ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hvj)
      rw [show eightEightShoreCoordinateEquiv G c hc a b hab u v
        huinj hvinj hurange hvrange (u i) = zmodEightLeftFin16 i by simp,
        show eightEightShoreCoordinateEquiv G c hc a b hab u v
        huinj hvinj hurange hvrange (v j) = zmodEightRightFin16 j by simp]
      exact iff_of_false hnot (eightEightCycleGraph_zmod_cross i j)
    · rw [← hvrange] at hxb
      rw [← hurange] at hya
      obtain ⟨i, rfl⟩ := hxb
      obtain ⟨j, rfl⟩ := hya
      have hnot : ¬H.Adj (v i) (u j) := by
        intro hadj
        apply hab
        have huj : H.connectedComponentMk (u j) = a :=
          (ConnectedComponent.mem_supp_iff a _).mp (by
            rw [← hurange]; exact ⟨j, rfl⟩)
        have hvi : H.connectedComponentMk (v i) = b :=
          (ConnectedComponent.mem_supp_iff b _).mp (by
            rw [← hvrange]; exact ⟨i, rfl⟩)
        exact huj.symm.trans
          ((ConnectedComponent.connectedComponentMk_eq_of_adj hadj.symm).trans hvi)
      rw [show eightEightShoreCoordinateEquiv G c hc a b hab u v
        huinj hvinj hurange hvrange (v i) = zmodEightRightFin16 i by simp,
        show eightEightShoreCoordinateEquiv G c hc a b hab u v
        huinj hvinj hurange hvrange (u j) = zmodEightLeftFin16 j by simp]
      exact iff_of_false hnot (fun h =>
        eightEightCycleGraph_zmod_cross j i h.symm)
    · rw [← hvrange] at hxb hyb
      obtain ⟨i, rfl⟩ := hxb
      obtain ⟨j, rfl⟩ := hyb
      rw [← H.mem_neighborFinset, hv]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rw [hvinj.eq_iff, hvinj.eq_iff]
      simpa only [eightEightShoreCoordinateEquiv_apply_v] using
        (eightEightCycleGraph_zmodRight_iff i j).symm

end

end Erdos85
