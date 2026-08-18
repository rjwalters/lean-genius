import Proofs.Erdos85MuThreeAllTfExteriorOccupiedCoordinates
import Proofs.Erdos85BinarySquareMuThreeExteriorRowHit

/-! # Exterior coordinate images imply the native grid hit counts -/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem mu3AllTfShapeCellEquiv_val (shape : Mu3AllTfShape) (i : Fin 48) :
    (mu3AllTfShapeCellEquiv shape i).1 = (mu3AllTfCells shape).getD i.val 0 := by
  revert i
  cases shape <;> native_decide

/-- Graph-facing data supplied by the two exterior hit-image theorems. -/
structure Mu3ExteriorHitImages {W : Type*} [Fintype W] [DecidableEq W]
    (shape : Mu3AllTfShape) (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : Fin 48 ≃ W) where
  rowCoord : W → Fin 8
  columnCoord : W → Fin 8
  coord : ∀ i,
    (rowCoord (e i)).val * 8 + (columnCoord (e i)).val =
      (mu3AllTfCells shape).getD i.val 0
  rowInjective : ∀ u,
    Set.InjOn rowCoord {v | G.Adj u v}
  columnInjective : ∀ u,
    Set.InjOn columnCoord {v | G.Adj u v}
  rowImage : ∀ u,
    (Finset.univ.filter fun v => G.Adj u v).image rowCoord =
      Finset.univ.filter fun x =>
        ¬ mu3AllTfInternal shape x.val (columnCoord u).val
  columnImage : ∀ u,
    (Finset.univ.filter fun v => G.Adj u v).image columnCoord =
      Finset.univ.filter fun y =>
        ¬ mu3AllTfInternal shape (rowCoord u).val y.val

theorem card_fiber_of_injOn_image_eq
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (t : Finset β)
    (hinj : Set.InjOn f s) (himage : s.image f = t) (b : β) :
    (s.filter fun a => f a = b).card = if b ∈ t then 1 else 0 := by
  classical
  by_cases hb : b ∈ t
  · have hbt : b ∈ t := hb
    rw [← himage] at hb
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hb
    have hfiber : s.filter (fun c => f c = b) = {a} := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hc, hfc⟩
        exact hinj hc ha (hfc.trans hfa.symm)
      · intro hca
        subst c
        exact ⟨ha, hfa⟩
    rw [hfiber]
    simp [hbt]
  · have hfiber : s.filter (fun a => f a = b) = ∅ := by
      ext a
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨ha, hfa⟩
      apply hb
      rw [← himage]
      exact Finset.mem_image.mpr ⟨a, ha, hfa⟩
    rw [hfiber]
    simp [hb]

theorem mu3ExteriorHitImages_row_fiber_card
    {W : Type*} [Fintype W] [DecidableEq W]
    (shape : Mu3AllTfShape) (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : Fin 48 ≃ W) (h : Mu3ExteriorHitImages shape G e)
    (u : W) (x : Fin 8) :
    (Finset.univ.filter fun v : W => G.Adj u v ∧ h.rowCoord v = x).card =
      if mu3AllTfInternal shape x.val (h.columnCoord u).val then 0 else 1 := by
  let s := Finset.univ.filter fun v : W => G.Adj u v
  have hinj : Set.InjOn h.rowCoord s := by
    simpa [s] using h.rowInjective u
  have hc := card_fiber_of_injOn_image_eq s h.rowCoord
    (Finset.univ.filter fun x : Fin 8 =>
      ¬ mu3AllTfInternal shape x.val (h.columnCoord u).val)
    hinj (h.rowImage u) x
  have hcard :
      (Finset.univ.filter fun v : W => G.Adj u v ∧ h.rowCoord v = x).card =
        (s.filter fun v => h.rowCoord v = x).card := by
    apply congrArg Finset.card
    ext v
    simp [s]
  rw [hcard]
  by_cases hh : mu3AllTfInternal shape x.val (h.columnCoord u).val
  · simpa [hh] using hc
  · simpa [hh] using hc

theorem mu3ExteriorHitImages_column_fiber_card
    {W : Type*} [Fintype W] [DecidableEq W]
    (shape : Mu3AllTfShape) (G : SimpleGraph W) [DecidableRel G.Adj]
    (e : Fin 48 ≃ W) (h : Mu3ExteriorHitImages shape G e)
    (u : W) (y : Fin 8) :
    (Finset.univ.filter fun v : W => G.Adj u v ∧ h.columnCoord v = y).card =
      if mu3AllTfInternal shape (h.rowCoord u).val y.val then 0 else 1 := by
  let s := Finset.univ.filter fun v : W => G.Adj u v
  have hinj : Set.InjOn h.columnCoord s := by
    simpa [s] using h.columnInjective u
  have hc := card_fiber_of_injOn_image_eq s h.columnCoord
    (Finset.univ.filter fun y : Fin 8 =>
      ¬ mu3AllTfInternal shape (h.rowCoord u).val y.val)
    hinj (h.columnImage u) y
  have hcard :
      (Finset.univ.filter fun v : W => G.Adj u v ∧ h.columnCoord v = y).card =
        (s.filter fun v => h.columnCoord v = y).card := by
    apply congrArg Finset.card
    ext v
    simp [s]
  rw [hcard]
  by_cases hh : mu3AllTfInternal shape (h.rowCoord u).val y.val
  · simpa [hh] using hc
  · simpa [hh] using hc

#print axioms card_fiber_of_injOn_image_eq
#print axioms mu3ExteriorHitImages_row_fiber_card
#print axioms mu3ExteriorHitImages_column_fiber_card

end

end Erdos85
