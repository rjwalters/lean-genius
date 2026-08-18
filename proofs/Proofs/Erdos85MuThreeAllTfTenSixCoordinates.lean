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

end Erdos85
