import Proofs.Erdos85MuThreeAllTfTenSixCoordinates

/-! # Signed coordinates for the connected `C16` all-TF shape -/

open SimpleGraph

namespace Erdos85

structure SixteenCycleLabeling {V : Type*} (H : SimpleGraph V) where
  toEquiv : V ≃ Fin 16
  map_adj_iff : ∀ u v,
    H.Adj u v ↔ (cycleGraph 16).Adj (toEquiv u) (toEquiv v)

def sixteenParityShift (shift : Bool) (i : Fin 16) : Fin 16 :=
  ⟨(i.val + if shift then 1 else 0) % 16,
    Nat.mod_lt _ (by omega)⟩

set_option maxRecDepth 100000 in
theorem sixteenParityShift_bijective : ∀ shift,
    Function.Bijective (sixteenParityShift shift) := by
  native_decide

noncomputable def sixteenParityShiftEquiv (shift : Bool) : Fin 16 ≃ Fin 16 :=
  Equiv.ofBijective (sixteenParityShift shift)
    (sixteenParityShift_bijective shift)

set_option maxRecDepth 100000 in
theorem sixteenParityShift_preserves_adj : ∀ shift u v,
    (cycleGraph 16).Adj (sixteenParityShift shift u)
        (sixteenParityShift shift v) ↔
      (cycleGraph 16).Adj u v := by
  native_decide

def sixteenSignAlignedIndex (sign : Fin 16 → Bool) (i : Fin 16) : Fin 16 :=
  sixteenParityShift (!sign 0) i

set_option maxRecDepth 100000 in
theorem sixteenSignAlignedIndex_parity :
    ∀ (sign : Fin 16 → Bool),
      (∀ u v, (cycleGraph 16).Adj u v → sign u ≠ sign v) →
      ∀ i, (sixteenSignAlignedIndex sign i).val % 2 =
        if sign i then 0 else 1 := by
  native_decide

set_option maxRecDepth 100000 in
theorem sixteenCycleGraph_even_odd_iff_mu3Internal :
    ∀ (i j : Fin 16), i.val % 2 = 0 → j.val % 2 = 1 →
      ((cycleGraph 16).Adj i j ↔
        mu3AllTfInternal .c16 (i.val / 2) (j.val / 2)) := by
  native_decide

def sixteenLabelSign
    {V : Type*} {H : SimpleGraph V}
    (label : SixteenCycleLabeling H) (s : V → ℤ) : Fin 16 → Bool :=
  fun i => decide (s (label.toEquiv.symm i) = 1)

noncomputable def sixteenAlignedVertexEquiv
    {V : Type*} {H : SimpleGraph V}
    (label : SixteenCycleLabeling H) (s : V → ℤ) : V ≃ Fin 16 :=
  label.toEquiv.trans
    (sixteenParityShiftEquiv (!sixteenLabelSign label s 0))

theorem sixteenLabelSign_flips
    {V : Type*} (H : SimpleGraph V)
    (label : SixteenCycleLabeling H) (s : V → ℤ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) :
    ∀ u v, (cycleGraph 16).Adj u v →
      sixteenLabelSign label s u ≠ sixteenLabelSign label s v := by
  intro u v huv
  have huvH : H.Adj (label.toEquiv.symm u) (label.toEquiv.symm v) := by
    apply (label.map_adj_iff _ _).2
    simpa using huv
  have hf := hflip huvH
  have hu := hsign (label.toEquiv.symm u)
  have hv := hsign (label.toEquiv.symm v)
  rcases hu with hu | hu <;> rcases hv with hv | hv <;>
    simp [sixteenLabelSign, hu, hv] at hf ⊢

theorem sixteenAlignedVertexEquiv_sign_iff_parity
    {V : Type*} (H : SimpleGraph V)
    (label : SixteenCycleLabeling H) (s : V → ℤ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) (x : V) :
    (s x = 1 ↔ (sixteenAlignedVertexEquiv label s x).val % 2 = 0) ∧
      (s x = -1 ↔ (sixteenAlignedVertexEquiv label s x).val % 2 = 1) := by
  let sign := sixteenLabelSign label s
  let i := label.toEquiv x
  have hp := sixteenSignAlignedIndex_parity sign
    (sixteenLabelSign_flips H label s hsign hflip) i
  have hs := hsign x
  rcases hs with hs | hs
  · have hsigni : sign i = false := by
      simp [sign, i, sixteenLabelSign, hs]
    simp [sixteenAlignedVertexEquiv, sixteenSignAlignedIndex,
      sign, i, hs, hsigni] at hp ⊢
    exact hp
  · have hsigni : sign i = true := by
      simp [sign, i, sixteenLabelSign, hs]
    simp [sixteenAlignedVertexEquiv, sixteenSignAlignedIndex,
      sign, i, hs, hsigni] at hp ⊢
    exact hp

noncomputable def sixteenInternalCoordinateModel
    {V : Type*} [DecidableEq V] (H : SimpleGraph V)
    (label : SixteenCycleLabeling H) (s : V → ℤ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) :
    Mu3InternalCoordinateModel H
      {x : V // s x = 1} {x : V // s x = -1}
      Subtype.val Subtype.val .c16 := by
  let aligned := sixteenAlignedVertexEquiv label s
  have hpos : ∀ x, s x = 1 ↔ (aligned x).val % 2 = 0 := fun x =>
    (sixteenAlignedVertexEquiv_sign_iff_parity H label s hsign hflip x).1
  have hneg : ∀ x, s x = -1 ↔ (aligned x).val % 2 = 1 := fun x =>
    (sixteenAlignedVertexEquiv_sign_iff_parity H label s hsign hflip x).2
  let row : {x : V // s x = 1} ≃ Fin 8 :=
    (aligned.subtypeEquiv hpos).trans evenFin16EquivFin8
  let column : {x : V // s x = -1} ≃ Fin 8 :=
    (aligned.subtypeEquiv hneg).trans oddFin16EquivFin8
  refine { row := row, column := column, hole_iff := ?_ }
  intro p n
  have hp : (aligned p.1).val % 2 = 0 := (hpos p.1).mp p.2
  have hn : (aligned n.1).val % 2 = 1 := (hneg n.1).mp n.2
  have hadjLabel := label.map_adj_iff p.1 n.1
  have hadjShift := sixteenParityShift_preserves_adj
    (!sixteenLabelSign label s 0) (label.toEquiv p.1) (label.toEquiv n.1)
  have hnative := sixteenCycleGraph_even_odd_iff_mu3Internal
    (aligned p.1) (aligned n.1) hp hn
  change H.Adj p.1 n.1 ↔
    mu3AllTfInternal .c16 ((aligned p.1).val / 2)
      ((aligned n.1).val / 2)
  exact hadjLabel.trans (hadjShift.symm.trans hnative)

end Erdos85
