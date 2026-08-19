import Proofs.Erdos85EightEightCoordinateCover
import Proofs.Erdos85EightEightLowExteriorModelIso
import Proofs.Erdos85SizeTwoEigenlineCycleCoordinateNormalization

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

private theorem finEight_shift_sign (i : Fin 8) :
    (-1 : ℤ) ^ (i + 1).val * (-1) = (-1 : ℤ) ^ i.val := by
  fin_cases i <;> decide

structure NormalizedEightShoreCoordinates
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (a : H.ConnectedComponent) (s : W → ℤ) where
  u : ZMod 8 → W
  injective : Function.Injective u
  range : Set.range u = a.supp
  neighbor : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)}
  sign : ∀ z, s (u z) = (-1 : ℤ) ^ ((ZMod.finEquiv 8).symm z).val

theorem zmodEightCoordinates_neighborFinset
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (a : H.ConnectedComponent)
    (e : Fin 8 ≃ a.supp)
    (he : ∀ i j, (cycleGraph 8).Adj i j ↔ H.Adj (e i).1 (e j).1) :
    let u : ZMod 8 → W := fun z => (e ((ZMod.finEquiv 8).symm z)).1
    ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)} := by
  dsimp only
  intro z
  ext y
  rw [H.mem_neighborFinset]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hzy
    have hyc : y ∈ a.supp :=
      (ConnectedComponent.mem_supp_congr_adj a hzy).mp
        (e ((ZMod.finEquiv 8).symm z)).2
    let j : Fin 8 := e.symm ⟨y, hyc⟩
    have hy : (e j).1 = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hyc⟩)
    have hcycle : (cycleGraph 8).Adj ((ZMod.finEquiv 8).symm z) j := by
      apply (he _ _).mpr
      simpa [hy] using hzy
    have hmem : j ∈ (cycleGraph 8).neighborFinset
        ((ZMod.finEquiv 8).symm z) :=
      ((cycleGraph 8).mem_neighborFinset _ _).mpr hcycle
    rw [cycleGraph_neighborFinset] at hmem
    rcases (by simpa using hmem) with hj | hj
    · left
      rw [← hy, hj]
      congr 2 <;> simp
    · right
      rw [← hy, hj]
      congr 2 <;> simp
  · rintro (rfl | rfl)
    · apply (he _ _).mp
      rw [← (cycleGraph 8).mem_neighborFinset,
        cycleGraph_neighborFinset]
      simp
    · apply (he _ _).mp
      rw [← (cycleGraph 8).mem_neighborFinset,
        cycleGraph_neighborFinset]
      simp

/-- Every signed eight-cycle admits positive-even-phase coordinates. -/
theorem exists_normalizedEightShoreCoordinates
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hdeg : ∀ x, H.degree x = 2)
    (a : H.ConnectedComponent) (ha : a.supp.ncard = 8)
    (s : W → ℤ)
    (hsign : ∀ x ∈ a.supp, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) :
    Nonempty (NormalizedEightShoreCoordinates H a s) := by
  obtain ⟨e, he, hs⟩ :=
    exists_componentCycleEquiv_sign_normalized H hdeg 4 (by omega) a
      (by simpa using ha) s hflip
  rcases hsign (e 0).1 (e 0).2 with hphase | hphase
  · let shift : Equiv.Perm (Fin 8) := Equiv.addRight 1
    let e' : Fin 8 ≃ a.supp := shift.trans e
    have he' : ∀ i j, (cycleGraph 8).Adj i j ↔
        H.Adj (e' i).1 (e' j).1 := by
      intro i j
      change (cycleGraph 8).Adj i j ↔ H.Adj (e (i + 1)).1 (e (j + 1)).1
      rw [← he]
      simp [cycleGraph_adj]
    let u : ZMod 8 → W := fun z => (e' ((ZMod.finEquiv 8).symm z)).1
    refine ⟨⟨u, ?_, ?_, ?_, ?_⟩⟩
    · intro x y hxy
      apply (ZMod.finEquiv 8).symm.injective
      apply e'.injective
      exact Subtype.ext hxy
    · ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact (e' ((ZMod.finEquiv 8).symm z)).2
      · intro hx
        obtain ⟨i, hi⟩ := e'.surjective ⟨x, hx⟩
        exact ⟨ZMod.finEquiv 8 i, congrArg Subtype.val hi⟩
    · exact zmodEightCoordinates_neighborFinset H a e' he'
    · intro z
      let i := (ZMod.finEquiv 8).symm z
      change s (e (i + 1)).1 = (-1 : ℤ) ^ i.val
      have hphase' : s (e ⟨0, by omega⟩).1 = -1 := by simpa using hphase
      rw [hs, hphase']
      exact finEight_shift_sign i
  · let u : ZMod 8 → W := fun z => (e ((ZMod.finEquiv 8).symm z)).1
    refine ⟨⟨u, ?_, ?_, ?_, ?_⟩⟩
    · intro x y hxy
      apply (ZMod.finEquiv 8).symm.injective
      apply e.injective
      exact Subtype.ext hxy
    · ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact (e ((ZMod.finEquiv 8).symm z)).2
      · intro hx
        obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
        exact ⟨ZMod.finEquiv 8 i, congrArg Subtype.val hi⟩
    · exact zmodEightCoordinates_neighborFinset H a e he
    · intro z
      have hphase' : s (e ⟨0, by omega⟩).1 = 1 := by simpa using hphase
      rw [hs, hphase', mul_one]

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
