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

end Erdos85
