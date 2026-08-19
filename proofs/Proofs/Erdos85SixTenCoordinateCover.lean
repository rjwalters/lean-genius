import Proofs.Erdos85SixTenMixedOwnerCnfBridge

/-! # Covering coordinates for two six-ten cycle shores -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

open SixTenMixedOwnerBridge

/-- Two disjoint injective C6 and C10 shore parametrizations cover a size-sixteen
component. -/
theorem sixTen_shores_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ x : c.supp, x ∈ a.supp ∨ x ∈ b.supp := by
  classical
  have himgu : (Finset.univ.image u).card = 6 := by
    rw [Finset.card_image_of_injective _ huinj, Finset.card_univ]
    simp
  have himgv : (Finset.univ.image v).card = 10 := by
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
def sixTenFromCoordinates
    {W : Type*} (u : ZMod 6 → W) (v : ZMod 10 → W) (x : Fin 16) : W :=
  match (finSumFinEquiv : Fin 6 ⊕ Fin 10 ≃ Fin 16).symm x with
  | Sum.inl i => u (ZMod.finEquiv 6 i)
  | Sum.inr j => v (ZMod.finEquiv 10 j)

@[simp] theorem sixTenFromCoordinates_left
    {W : Type*} (u : ZMod 6 → W) (v : ZMod 10 → W) (i : ZMod 6) :
    sixTenFromCoordinates u v (zmodSixLeftFin16 i) = u i := by
  unfold sixTenFromCoordinates
  rw [show (finSumFinEquiv : Fin 6 ⊕ Fin 10 ≃ Fin 16).symm
      (zmodSixLeftFin16 i) = Sum.inl ((ZMod.finEquiv 6).symm i) by
    apply (finSumFinEquiv : Fin 6 ⊕ Fin 10 ≃ Fin 16).injective
    simpa [zmodSixLeftFin16] using
      (finSumFinEquiv_apply_left (m := 6) (n := 10)
        ((ZMod.finEquiv 6).symm i)).symm]
  simp

@[simp] theorem sixTenFromCoordinates_right
    {W : Type*} (u : ZMod 6 → W) (v : ZMod 10 → W) (j : ZMod 10) :
    sixTenFromCoordinates u v (zmodTenRightFin16 j) = v j := by
  unfold sixTenFromCoordinates
  rw [show (finSumFinEquiv : Fin 6 ⊕ Fin 10 ≃ Fin 16).symm
      (zmodTenRightFin16 j) = Sum.inr ((ZMod.finEquiv 10).symm j) by
    apply (finSumFinEquiv : Fin 6 ⊕ Fin 10 ≃ Fin 16).injective
    simpa [zmodTenRightFin16] using
      (finSumFinEquiv_apply_right (m := 6) (n := 10)
        ((ZMod.finEquiv 10).symm j)).symm]
  simp

/-- The two shore parametrizations canonically produce the exact covering
equivalence expected by the fixed owner model. -/
noncomputable def sixTenShoreCoordinateEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    c.supp ≃ Fin 16 :=
  let f := sixTenFromCoordinates u v
  let hcover := sixTen_shores_cover G c hc a b hab u v huinj hvinj
    hurange hvrange
  (Equiv.ofBijective f (by
    constructor
    · intro x y hxy
      rcases hx : (finSumFinEquiv : Fin 6 ⊕ Fin 10 ≃ Fin 16).symm x with i | j <;>
        rcases hy : (finSumFinEquiv : Fin 6 ⊕ Fin 10 ≃ Fin 16).symm y with i' | j'
      · apply (finSumFinEquiv : Fin 6 ⊕ Fin 10 ≃ Fin 16).symm.injective
        rw [hx, hy]
        congr 1
        apply (ZMod.finEquiv 6).injective
        apply huinj
        simpa [f, sixTenFromCoordinates, hx, hy] using hxy
      · exfalso
        have hua : f x ∈ a.supp := by
          rw [← hurange]
          exact ⟨ZMod.finEquiv 6 i, by simp [f, sixTenFromCoordinates, hx]⟩
        have hvb : f y ∈ b.supp := by
          rw [← hvrange]
          exact ⟨ZMod.finEquiv 10 j', by simp [f, sixTenFromCoordinates, hy]⟩
        exact hab (ConnectedComponent.eq_of_common_vertex
          (hxy ▸ hua) hvb)
      · exfalso
        have hvb : f x ∈ b.supp := by
          rw [← hvrange]
          exact ⟨ZMod.finEquiv 10 j, by simp [f, sixTenFromCoordinates, hx]⟩
        have hua : f y ∈ a.supp := by
          rw [← hurange]
          exact ⟨ZMod.finEquiv 6 i', by simp [f, sixTenFromCoordinates, hy]⟩
        exact hab (ConnectedComponent.eq_of_common_vertex
          hua (hxy ▸ hvb))
      · apply (finSumFinEquiv : Fin 6 ⊕ Fin 10 ≃ Fin 16).symm.injective
        rw [hx, hy]
        congr 1
        apply (ZMod.finEquiv 10).injective
        apply hvinj
        simpa [f, sixTenFromCoordinates, hx, hy] using hxy
    · intro x
      rcases hcover x with hxa | hxb
      · rw [← hurange] at hxa
        obtain ⟨i, rfl⟩ := hxa
        exact ⟨zmodSixLeftFin16 i, by simp [f]⟩
      · rw [← hvrange] at hxb
        obtain ⟨j, rfl⟩ := hxb
        exact ⟨zmodTenRightFin16 j, by simp [f]⟩)).symm

@[simp] theorem sixTenShoreCoordinateEquiv_apply_u
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (i : ZMod 6) :
    sixTenShoreCoordinateEquiv G c hc a b hab u v huinj hvinj
      hurange hvrange (u i) = zmodSixLeftFin16 i := by
  apply (sixTenShoreCoordinateEquiv G c hc a b hab u v huinj hvinj
    hurange hvrange).symm.injective
  simp [sixTenShoreCoordinateEquiv]

@[simp] theorem sixTenShoreCoordinateEquiv_apply_v
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (j : ZMod 10) :
    sixTenShoreCoordinateEquiv G c hc a b hab u v huinj hvinj
      hurange hvrange (v j) = zmodTenRightFin16 j := by
  apply (sixTenShoreCoordinateEquiv G c hc a b hab u v huinj hvinj
    hurange hvrange).symm.injective
  simp [sixTenShoreCoordinateEquiv]

end


end Erdos85

#print axioms Erdos85.sixTen_shores_cover
#print axioms Erdos85.sixTenShoreCoordinateEquiv_apply_u
