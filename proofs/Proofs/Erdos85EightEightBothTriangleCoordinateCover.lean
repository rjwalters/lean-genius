import Proofs.Erdos85EightEightBothTriangleOwnerCnfBridge

/-! # Both-triangle covering coordinates for two eight-cycle shores -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

open BothTriangleOwnerBridge

/-- Two disjoint injective eight-shore parametrizations cover a size-sixteen
component. -/
theorem bothTriangleEight_shores_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ x : c.supp, x ∈ a.supp ∨ x ∈ b.supp := by
  classical
  have himgu : (Finset.univ.image u).card = 8 := by
    rw [Finset.card_image_of_injective _ huinj, Finset.card_univ]
    simp
  have himgv : (Finset.univ.image v).card = 8 := by
    rw [Finset.card_image_of_injective _ hvinj, Finset.card_univ]
    simp
  have hdisj : Disjoint (Finset.univ.image u) (Finset.univ.image v) := by
    rw [Finset.disjoint_left]
    rintro x hx hx'
    rw [Finset.mem_image] at hx hx'
    obtain ⟨i, -, hi⟩ := hx
    obtain ⟨j, -, hj⟩ := hx'
    have hxa : x ∈ a.supp := by rw [← hurange]; exact ⟨i, hi⟩
    have hxb : x ∈ b.supp := by rw [← hvrange]; exact ⟨j, hj⟩
    exact hab (ConnectedComponent.eq_of_common_vertex hxa hxb)
  have hcardSupp : Fintype.card c.supp = 16 := by
    simpa [Set.ncard_eq_toFinset_card'] using hc
  have huniv : Finset.univ.image u ∪ Finset.univ.image v =
      (Finset.univ : Finset c.supp) := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj, himgu, himgv]
    simpa [hcardSupp]
  intro x
  have hx : x ∈ Finset.univ.image u ∪ Finset.univ.image v := by
    rw [huniv]
    exact Finset.mem_univ x
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
  rcases hx with ⟨i, -, hi⟩ | ⟨j, -, hj⟩
  · left; rw [← hurange]; exact ⟨i, hi⟩
  · right; rw [← hvrange]; exact ⟨j, hj⟩

/-- Decode the fixed two-shore `Fin 16` coordinates through cyclic maps. -/
def bothTriangleEightFromCoordinates
    {W : Type*} (u v : ZMod 8 → W) (x : Fin 16) : W :=
  match (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).symm x with
  | Sum.inl i => u (ZMod.finEquiv 8 i)
  | Sum.inr j => v (ZMod.finEquiv 8 j)

@[simp] theorem bothTriangleEightFromCoordinates_left
    {W : Type*} (u v : ZMod 8 → W) (i : ZMod 8) :
    bothTriangleEightFromCoordinates u v (zmodEightLeftFin16 i) = u i := by
  unfold bothTriangleEightFromCoordinates
  rw [show (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).symm
      (zmodEightLeftFin16 i) = Sum.inl ((ZMod.finEquiv 8).symm i) by
    apply (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).injective
    simpa [zmodEightLeftFin16] using
      (finSumFinEquiv_apply_left (m := 8) (n := 8)
        ((ZMod.finEquiv 8).symm i)).symm]
  simp

@[simp] theorem bothTriangleEightFromCoordinates_right
    {W : Type*} (u v : ZMod 8 → W) (j : ZMod 8) :
    bothTriangleEightFromCoordinates u v (zmodEightRightFin16 j) = v j := by
  unfold bothTriangleEightFromCoordinates
  rw [show (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).symm
      (zmodEightRightFin16 j) = Sum.inr ((ZMod.finEquiv 8).symm j) by
    apply (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).injective
    simpa [zmodEightRightFin16] using
      (finSumFinEquiv_apply_right (m := 8) (n := 8)
        ((ZMod.finEquiv 8).symm j)).symm]
  simp

/-- The two shore parametrizations canonically produce the exact covering
equivalence expected by the fixed owner model. -/
noncomputable def bothTriangleEightShoreCoordinateEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    c.supp ≃ Fin 16 :=
  let f := bothTriangleEightFromCoordinates u v
  let hcover := bothTriangleEight_shores_cover G c hc a b hab u v huinj hvinj
    hurange hvrange
  (Equiv.ofBijective f (by
    constructor
    · intro x y hxy
      rcases hx : (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).symm x with i | j <;>
        rcases hy : (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).symm y with i' | j'
      · apply (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).symm.injective
        rw [hx, hy]
        congr 1
        apply (ZMod.finEquiv 8).injective
        apply huinj
        simpa [f, bothTriangleEightFromCoordinates, hx, hy] using hxy
      · exfalso
        have hua : f x ∈ a.supp := by
          rw [← hurange]
          exact ⟨ZMod.finEquiv 8 i, by simp [f, bothTriangleEightFromCoordinates, hx]⟩
        have hvb : f y ∈ b.supp := by
          rw [← hvrange]
          exact ⟨ZMod.finEquiv 8 j', by simp [f, bothTriangleEightFromCoordinates, hy]⟩
        exact hab (ConnectedComponent.eq_of_common_vertex
          (hxy ▸ hua) hvb)
      · exfalso
        have hvb : f x ∈ b.supp := by
          rw [← hvrange]
          exact ⟨ZMod.finEquiv 8 j, by simp [f, bothTriangleEightFromCoordinates, hx]⟩
        have hua : f y ∈ a.supp := by
          rw [← hurange]
          exact ⟨ZMod.finEquiv 8 i', by simp [f, bothTriangleEightFromCoordinates, hy]⟩
        exact hab (ConnectedComponent.eq_of_common_vertex
          hua (hxy ▸ hvb))
      · apply (finSumFinEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16).symm.injective
        rw [hx, hy]
        congr 1
        apply (ZMod.finEquiv 8).injective
        apply hvinj
        simpa [f, bothTriangleEightFromCoordinates, hx, hy] using hxy
    · intro x
      rcases hcover x with hxa | hxb
      · rw [← hurange] at hxa
        obtain ⟨i, rfl⟩ := hxa
        exact ⟨zmodEightLeftFin16 i, by simp [f]⟩
      · rw [← hvrange] at hxb
        obtain ⟨j, rfl⟩ := hxb
        exact ⟨zmodEightRightFin16 j, by simp [f]⟩)).symm

@[simp] theorem bothTriangleEightShoreCoordinateEquiv_apply_u
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (i : ZMod 8) :
    bothTriangleEightShoreCoordinateEquiv G c hc a b hab u v huinj hvinj
      hurange hvrange (u i) = zmodEightLeftFin16 i := by
  apply (bothTriangleEightShoreCoordinateEquiv G c hc a b hab u v huinj hvinj
    hurange hvrange).symm.injective
  simp [bothTriangleEightShoreCoordinateEquiv]

@[simp] theorem bothTriangleEightShoreCoordinateEquiv_apply_v
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (j : ZMod 8) :
    bothTriangleEightShoreCoordinateEquiv G c hc a b hab u v huinj hvinj
      hurange hvrange (v j) = zmodEightRightFin16 j := by
  apply (bothTriangleEightShoreCoordinateEquiv G c hc a b hab u v huinj hvinj
    hurange hvrange).symm.injective
  simp [bothTriangleEightShoreCoordinateEquiv]

end


end Erdos85

#print axioms Erdos85.bothTriangleEight_shores_cover
#print axioms Erdos85.bothTriangleEightShoreCoordinateEquiv_apply_u
