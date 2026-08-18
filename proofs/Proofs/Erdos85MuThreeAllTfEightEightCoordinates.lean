import Proofs.Erdos85MuThreeAllTfTenSixCoordinates

/-! # Signed coordinates for the `C8 + C8` all-TF shape -/

open SimpleGraph

namespace Erdos85

def eightEightAdj (u v : Fin 16) : Bool :=
  if u.val < 8 then
    v.val < 8 &&
      (v.val = (u.val + 1) % 8 || u.val = (v.val + 1) % 8)
  else
    8 ≤ v.val &&
      ((v.val - 8) = (u.val - 8 + 1) % 8 ||
        (u.val - 8) = (v.val - 8 + 1) % 8)

theorem eightEightAdj_symmetric : ∀ u v,
    eightEightAdj u v = eightEightAdj v u := by native_decide

theorem eightEightAdj_loopless : ∀ u, eightEightAdj u u = false := by
  native_decide

def eightEightCycleGraph : SimpleGraph (Fin 16) where
  Adj u v := eightEightAdj u v = true
  symm := ⟨by
    intro u v h
    rw [← eightEightAdj_symmetric]
    exact h⟩
  loopless := ⟨by
    intro u h
    rw [eightEightAdj_loopless] at h
    contradiction⟩

instance : DecidableRel eightEightCycleGraph.Adj := by
  intro u v
  change Decidable (eightEightAdj u v = true)
  infer_instance

structure EightEightCycleLabeling {V : Type*} (H : SimpleGraph V) where
  toEquiv : V ≃ Fin 16
  map_adj_iff : ∀ u v,
    H.Adj u v ↔ eightEightCycleGraph.Adj (toEquiv u) (toEquiv v)

def eightEightParityShift (shift0 shift1 : Bool) (i : Fin 16) : Fin 16 :=
  if hi : i.val < 8 then
    ⟨(i.val + if shift0 then 1 else 0) % 8, by
      have := Nat.mod_lt (i.val + if shift0 then 1 else 0) (by omega : 0 < 8)
      omega⟩
  else
    ⟨8 + ((i.val - 8 + if shift1 then 1 else 0) % 8), by
      have := Nat.mod_lt (i.val - 8 + if shift1 then 1 else 0) (by omega : 0 < 8)
      omega⟩

set_option maxRecDepth 100000 in
theorem eightEightParityShift_bijective : ∀ a b,
    Function.Bijective (eightEightParityShift a b) := by native_decide

noncomputable def eightEightParityShiftEquiv (a b : Bool) : Fin 16 ≃ Fin 16 :=
  Equiv.ofBijective (eightEightParityShift a b)
    (eightEightParityShift_bijective a b)

set_option maxRecDepth 100000 in
theorem eightEightParityShift_preserves_adj : ∀ a b u v,
    eightEightCycleGraph.Adj (eightEightParityShift a b u)
        (eightEightParityShift a b v) ↔ eightEightCycleGraph.Adj u v := by
  native_decide

def eightEightSignAlignedIndex (sign : Fin 16 → Bool) (i : Fin 16) : Fin 16 :=
  eightEightParityShift (!sign 0) (!sign 8) i

set_option maxRecDepth 100000 in
theorem eightEightSignAlignedIndex_parity :
    ∀ (sign : Fin 16 → Bool),
      (∀ u v, eightEightCycleGraph.Adj u v → sign u ≠ sign v) →
      ∀ i, (eightEightSignAlignedIndex sign i).val % 2 =
        if sign i then 0 else 1 := by native_decide

set_option maxRecDepth 100000 in
theorem eightEightCycleGraph_even_odd_iff_mu3Internal :
    ∀ (i j : Fin 16), i.val % 2 = 0 → j.val % 2 = 1 →
      (eightEightCycleGraph.Adj i j ↔
        mu3AllTfInternal .c8c8 (i.val / 2) (j.val / 2)) := by
  native_decide

def eightEightLabelSign
    {V : Type*} {H : SimpleGraph V}
    (label : EightEightCycleLabeling H) (s : V → ℤ) : Fin 16 → Bool :=
  fun i => decide (s (label.toEquiv.symm i) = 1)

noncomputable def eightEightAlignedVertexEquiv
    {V : Type*} {H : SimpleGraph V}
    (label : EightEightCycleLabeling H) (s : V → ℤ) : V ≃ Fin 16 :=
  label.toEquiv.trans
    (eightEightParityShiftEquiv (!eightEightLabelSign label s 0)
      (!eightEightLabelSign label s 8))

theorem eightEightLabelSign_flips
    {V : Type*} (H : SimpleGraph V)
    (label : EightEightCycleLabeling H) (s : V → ℤ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) :
    ∀ u v, eightEightCycleGraph.Adj u v →
      eightEightLabelSign label s u ≠ eightEightLabelSign label s v := by
  intro u v huv
  have huvH : H.Adj (label.toEquiv.symm u) (label.toEquiv.symm v) := by
    apply (label.map_adj_iff _ _).2
    simpa using huv
  have hf := hflip huvH
  have hu := hsign (label.toEquiv.symm u)
  have hv := hsign (label.toEquiv.symm v)
  rcases hu with hu | hu <;> rcases hv with hv | hv <;>
    simp [eightEightLabelSign, hu, hv] at hf ⊢

theorem eightEightAlignedVertexEquiv_sign_iff_parity
    {V : Type*} (H : SimpleGraph V)
    (label : EightEightCycleLabeling H) (s : V → ℤ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) (x : V) :
    (s x = 1 ↔ (eightEightAlignedVertexEquiv label s x).val % 2 = 0) ∧
      (s x = -1 ↔ (eightEightAlignedVertexEquiv label s x).val % 2 = 1) := by
  let sign := eightEightLabelSign label s
  let i := label.toEquiv x
  have hp := eightEightSignAlignedIndex_parity sign
    (eightEightLabelSign_flips H label s hsign hflip) i
  have hs := hsign x
  rcases hs with hs | hs
  · have hsigni : sign i = false := by
      simp [sign, i, eightEightLabelSign, hs]
    simp [eightEightAlignedVertexEquiv, eightEightSignAlignedIndex,
      sign, i, hs, hsigni] at hp ⊢
    exact hp
  · have hsigni : sign i = true := by
      simp [sign, i, eightEightLabelSign, hs]
    simp [eightEightAlignedVertexEquiv, eightEightSignAlignedIndex,
      sign, i, hs, hsigni] at hp ⊢
    exact hp

noncomputable def eightEightInternalCoordinateModel
    {V : Type*} [DecidableEq V] (H : SimpleGraph V)
    (label : EightEightCycleLabeling H) (s : V → ℤ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) :
    Mu3InternalCoordinateModel H
      {x : V // s x = 1} {x : V // s x = -1}
      Subtype.val Subtype.val .c8c8 := by
  let aligned := eightEightAlignedVertexEquiv label s
  have hpos : ∀ x, s x = 1 ↔ (aligned x).val % 2 = 0 := fun x =>
    (eightEightAlignedVertexEquiv_sign_iff_parity H label s hsign hflip x).1
  have hneg : ∀ x, s x = -1 ↔ (aligned x).val % 2 = 1 := fun x =>
    (eightEightAlignedVertexEquiv_sign_iff_parity H label s hsign hflip x).2
  let row : {x : V // s x = 1} ≃ Fin 8 :=
    (aligned.subtypeEquiv hpos).trans evenFin16EquivFin8
  let column : {x : V // s x = -1} ≃ Fin 8 :=
    (aligned.subtypeEquiv hneg).trans oddFin16EquivFin8
  refine { row := row, column := column, hole_iff := ?_ }
  intro p n
  have hp : (aligned p.1).val % 2 = 0 := (hpos p.1).mp p.2
  have hn : (aligned n.1).val % 2 = 1 := (hneg n.1).mp n.2
  have hadjLabel := label.map_adj_iff p.1 n.1
  have hadjShift := eightEightParityShift_preserves_adj
    (!eightEightLabelSign label s 0) (!eightEightLabelSign label s 8)
      (label.toEquiv p.1) (label.toEquiv n.1)
  have hnative := eightEightCycleGraph_even_odd_iff_mu3Internal
    (aligned p.1) (aligned n.1) hp hn
  change H.Adj p.1 n.1 ↔
    mu3AllTfInternal .c8c8 ((aligned p.1).val / 2)
      ((aligned n.1).val / 2)
  exact hadjLabel.trans (hadjShift.symm.trans hnative)

end Erdos85
