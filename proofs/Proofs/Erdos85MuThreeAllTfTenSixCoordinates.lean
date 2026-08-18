import Proofs.Erdos85MuThreeAllTfExteriorOccupiedCoordinates
import Proofs.Erdos85OrderSixtyFourTenSixComponentLabeling

/-! # Parity coordinates for the `C10 + C6` all-TF shape -/

open SimpleGraph

namespace Erdos85

def evenFin16ToFin8 (i : {i : Fin 16 // i.val % 2 = 0}) : Fin 8 :=
  ⟨i.1.val / 2, Nat.div_lt_of_lt_mul i.1.isLt⟩

def fin8ToEvenFin16 (i : Fin 8) : {i : Fin 16 // i.val % 2 = 0} :=
  ⟨⟨2 * i.val, by omega⟩, by simp⟩

def evenFin16EquivFin8 : {i : Fin 16 // i.val % 2 = 0} ≃ Fin 8 where
  toFun := evenFin16ToFin8
  invFun := fin8ToEvenFin16
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change 2 * (i.1.val / 2) = i.1.val
    omega
  right_inv i := by
    apply Fin.ext
    change (2 * i.val) / 2 = i.val
    omega

def oddFin16ToFin8 (i : {i : Fin 16 // i.val % 2 = 1}) : Fin 8 :=
  ⟨i.1.val / 2, Nat.div_lt_of_lt_mul i.1.isLt⟩

def fin8ToOddFin16 (i : Fin 8) : {i : Fin 16 // i.val % 2 = 1} :=
  ⟨⟨2 * i.val + 1, by omega⟩, by simp⟩

def oddFin16EquivFin8 : {i : Fin 16 // i.val % 2 = 1} ≃ Fin 8 where
  toFun := oddFin16ToFin8
  invFun := fin8ToOddFin16
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change 2 * (i.1.val / 2) + 1 = i.1.val
    omega
  right_inv i := by
    apply Fin.ext
    change (2 * i.val + 1) / 2 = i.val
    omega

/- Closed finite audit: after splitting the standard `C10 + C6` labeling
by cyclic parity, its cross edges are precisely the native shape holes. -/
theorem tenSixCycleGraph_even_odd_iff_mu3Internal :
    ∀ (i j : Fin 16), i.val % 2 = 0 → j.val % 2 = 1 →
      (tenSixCycleGraph.Adj i j ↔
        mu3AllTfInternal .c10c6 (i.val / 2) (j.val / 2)) := by
  native_decide

/-- Independently rotate the ten- and six-cycles by zero or one step. -/
def tenSixParityShift (shift10 shift6 : Bool) (i : Fin 16) : Fin 16 :=
  if hi : i.val < 10 then
    ⟨(i.val + if shift10 then 1 else 0) % 10, by
      have := Nat.mod_lt (i.val + if shift10 then 1 else 0) (by omega : 0 < 10)
      omega⟩
  else
    ⟨10 + ((i.val - 10 + if shift6 then 1 else 0) % 6), by
      have := Nat.mod_lt (i.val - 10 + if shift6 then 1 else 0) (by omega : 0 < 6)
      omega⟩

set_option maxRecDepth 100000 in
theorem tenSixParityShift_bijective :
    ∀ shift10 shift6,
      Function.Bijective (tenSixParityShift shift10 shift6) := by
  native_decide

noncomputable def tenSixParityShiftEquiv (shift10 shift6 : Bool) :
    Fin 16 ≃ Fin 16 :=
  Equiv.ofBijective (tenSixParityShift shift10 shift6)
    (tenSixParityShift_bijective shift10 shift6)

set_option maxRecDepth 100000 in
theorem tenSixParityShift_preserves_adj :
    ∀ shift10 shift6 u v,
      tenSixCycleGraph.Adj
          (tenSixParityShift shift10 shift6 u)
          (tenSixParityShift shift10 shift6 v) ↔
        tenSixCycleGraph.Adj u v := by
  native_decide

/-- Choose the component rotations from the signs at standard vertices zero
and ten. -/
def tenSixSignAlignedIndex (sign : Fin 16 → Bool) (i : Fin 16) : Fin 16 :=
  tenSixParityShift (!sign 0) (!sign 10) i

/- Finite propagation audit: any Boolean signing flipped across every edge
becomes `true = even`, `false = odd` after the chosen component rotations. -/
set_option maxRecDepth 100000 in
theorem tenSixSignAlignedIndex_parity :
    ∀ (sign : Fin 16 → Bool),
      (∀ u v, tenSixCycleGraph.Adj u v → sign u ≠ sign v) →
      ∀ i, (tenSixSignAlignedIndex sign i).val % 2 =
        if sign i then 0 else 1 := by
  native_decide

noncomputable def tenSixSignAlignedEquiv (sign : Fin 16 → Bool) :
    Fin 16 ≃ Fin 16 :=
  (tenSixParityShiftEquiv (!sign 0) (!sign 10))

theorem tenSixSignAlignedEquiv_preserves_adj
    (sign : Fin 16 → Bool) (u v : Fin 16) :
    tenSixCycleGraph.Adj (tenSixSignAlignedEquiv sign u)
        (tenSixSignAlignedEquiv sign v) ↔
      tenSixCycleGraph.Adj u v :=
  tenSixParityShift_preserves_adj _ _ _ _

def tenSixLabelSign
    {V : Type*} {H : SimpleGraph V}
    (label : TenSixComponentLabeling H) (s : V → ℤ) : Fin 16 → Bool :=
  fun i => decide (s (label.toEquiv.symm i) = 1)

noncomputable def tenSixAlignedVertexEquiv
    {V : Type*} {H : SimpleGraph V}
    (label : TenSixComponentLabeling H) (s : V → ℤ) : V ≃ Fin 16 :=
  label.toEquiv.trans (tenSixSignAlignedEquiv (tenSixLabelSign label s))

theorem tenSixLabelSign_flips
    {V : Type*} (H : SimpleGraph V)
    (label : TenSixComponentLabeling H) (s : V → ℤ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) :
    ∀ u v, tenSixCycleGraph.Adj u v →
      tenSixLabelSign label s u ≠ tenSixLabelSign label s v := by
  intro u v huv
  have huvH : H.Adj (label.toEquiv.symm u) (label.toEquiv.symm v) := by
    apply (label.map_adj_iff _ _).2
    simpa using huv
  have hf := hflip huvH
  have hu := hsign (label.toEquiv.symm u)
  have hv := hsign (label.toEquiv.symm v)
  rcases hu with hu | hu <;> rcases hv with hv | hv <;>
    simp [tenSixLabelSign, hu, hv] at hf ⊢

theorem tenSixAlignedVertexEquiv_sign_iff_parity
    {V : Type*} (H : SimpleGraph V)
    (label : TenSixComponentLabeling H) (s : V → ℤ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) (x : V) :
    (s x = 1 ↔ (tenSixAlignedVertexEquiv label s x).val % 2 = 0) ∧
      (s x = -1 ↔ (tenSixAlignedVertexEquiv label s x).val % 2 = 1) := by
  let sign := tenSixLabelSign label s
  let i := label.toEquiv x
  have hp := tenSixSignAlignedIndex_parity sign
    (tenSixLabelSign_flips H label s hsign hflip) i
  have hs := hsign x
  rcases hs with hs | hs
  · have hsigni : sign i = false := by
      simp [sign, i, tenSixLabelSign, hs]
    simp [tenSixAlignedVertexEquiv, tenSixSignAlignedEquiv,
      tenSixSignAlignedIndex, sign, i, hs, hsigni] at hp ⊢
    exact hp
  · have hsigni : sign i = true := by
      simp [sign, i, tenSixLabelSign, hs]
    simp [tenSixAlignedVertexEquiv, tenSixSignAlignedEquiv,
      tenSixSignAlignedIndex, sign, i, hs, hsigni] at hp ⊢
    exact hp

/-- A signed `[10,6]` component labeling supplies the exact native grid
coordinate model. -/
noncomputable def tenSixInternalCoordinateModel
    {V : Type*} [DecidableEq V] (H : SimpleGraph V)
    (label : TenSixComponentLabeling H) (s : V → ℤ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) :
    Mu3InternalCoordinateModel H
      {x : V // s x = 1} {x : V // s x = -1}
      Subtype.val Subtype.val .c10c6 := by
  let aligned := tenSixAlignedVertexEquiv label s
  have hpos : ∀ x, s x = 1 ↔ (aligned x).val % 2 = 0 := fun x =>
    (tenSixAlignedVertexEquiv_sign_iff_parity H label s hsign hflip x).1
  have hneg : ∀ x, s x = -1 ↔ (aligned x).val % 2 = 1 := fun x =>
    (tenSixAlignedVertexEquiv_sign_iff_parity H label s hsign hflip x).2
  let row : {x : V // s x = 1} ≃ Fin 8 :=
    (aligned.subtypeEquiv hpos).trans evenFin16EquivFin8
  let column : {x : V // s x = -1} ≃ Fin 8 :=
    (aligned.subtypeEquiv hneg).trans oddFin16EquivFin8
  refine { row := row, column := column, hole_iff := ?_ }
  intro p n
  have hp : (aligned p.1).val % 2 = 0 := (hpos p.1).mp p.2
  have hn : (aligned n.1).val % 2 = 1 := (hneg n.1).mp n.2
  have hadjLabel := label.map_adj_iff p.1 n.1
  have hadjShift := tenSixSignAlignedEquiv_preserves_adj
    (tenSixLabelSign label s) (label.toEquiv p.1) (label.toEquiv n.1)
  have hnative := tenSixCycleGraph_even_odd_iff_mu3Internal
    (aligned p.1) (aligned n.1) hp hn
  change H.Adj p.1 n.1 ↔
    mu3AllTfInternal .c10c6 ((aligned p.1).val / 2)
      ((aligned n.1).val / 2)
  exact hadjLabel.trans (hadjShift.symm.trans hnative)

end Erdos85
