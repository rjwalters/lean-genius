import Proofs.Erdos85EightEightLowOwnerCnfBridge
import Proofs.Erdos85MuThreeAllTfEightEightCoordinates

/-!
# Phase alignment for the fixed low-eight exterior-pair model

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

An arbitrary pair of cyclic shore coordinates need not initially use the
same sign phase as the certificate's parity convention.  The existing
`eightEightAlignedVertexEquiv` independently rotates each shore by one step
when necessary.  This file proves that this phase alignment transports the
intrinsic low-`8+8` exterior-pair description to the exact fixed `Fin 16`
owner graph consumed by the checked CNF.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Executable characterization of the fixed owner graph: offset `±3`
inside either shore, and opposite parity between shores. -/
theorem eightEightLowExteriorPairGraph_adj_iff (x y : Fin 16) :
    eightEightLowExteriorPairGraph.Adj x y ↔
      (x.val / 8 = y.val / 8 ∧
        ((y.val + 8 - x.val) % 8 = 3 ∨
          (y.val + 8 - x.val) % 8 = 5)) ∨
      (x.val / 8 ≠ y.val / 8 ∧ x.val % 2 ≠ y.val % 2) := by
  revert x y
  decide

/-- Independent one-step rotations preserve the fixed within-shore owner
relation. -/
theorem eightEightParityShift_preserves_lowExterior_within
    (p q : Bool) (x y : Fin 16) (hshore : x.val / 8 = y.val / 8) :
    eightEightLowExteriorPairGraph.Adj
        (eightEightParityShift p q x) (eightEightParityShift p q y) ↔
      eightEightLowExteriorPairGraph.Adj x y := by
  revert p q x y
  decide

/-- Independent shore rotations preserve whether two coordinates lie on
the same shore. -/
theorem eightEightParityShift_sameShore_iff
    (p q : Bool) (x y : Fin 16) :
    (eightEightParityShift p q x).val / 8 =
        (eightEightParityShift p q y).val / 8 ↔
      x.val / 8 = y.val / 8 := by
  revert p q x y
  decide

/-- In sign-aligned coordinates, unequal eigenline signs are exactly
unequal coordinate parity. -/
theorem eightEightAlignedVertexEquiv_sign_ne_iff_parity_ne
    {V : Type*} (H : SimpleGraph V)
    (label : EightEightCycleLabeling H) (s : V → ℤ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y) (x y : V) :
    s x ≠ s y ↔
      (eightEightAlignedVertexEquiv label s x).val % 2 ≠
        (eightEightAlignedVertexEquiv label s y).val % 2 := by
  have hx := eightEightAlignedVertexEquiv_sign_iff_parity
    H label s hsign hflip x
  have hy := eightEightAlignedVertexEquiv_sign_iff_parity
    H label s hsign hflip y
  rcases hsign x with hxneg | hxpos <;>
    rcases hsign y with hyneg | hypos <;> simp_all

/-- Phase-alignment adapter.  The input is the intrinsic model in any
cycle labeling: on a common shore it already has the fixed offset-`±3`
relation, while across shores it is sign inequality.  The output is the
pointwise fixed-model theorem required by `lowEightExteriorPairModelIso`.

This isolates the only nontrivial nuisance in constructing the final graph
isomorphism: the two cyclic labelings may begin with unrelated sign phases. -/
theorem eightEightLowExteriorPair_model_of_cycleLabeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (R H : SimpleGraph V)
    (label : EightEightCycleLabeling H) (s : V → ℤ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hflip : ∀ ⦃x y⦄, H.Adj x y → s x = -s y)
    (hmodel : ∀ x y,
      R.Adj x y ↔
        if (label.toEquiv x).val / 8 = (label.toEquiv y).val / 8 then
          eightEightLowExteriorPairGraph.Adj
            (label.toEquiv x) (label.toEquiv y)
        else s x ≠ s y) :
    ∀ x y, R.Adj x y ↔
      eightEightLowExteriorPairGraph.Adj
        (eightEightAlignedVertexEquiv label s x)
        (eightEightAlignedVertexEquiv label s y) := by
  intro x y
  let p := !eightEightLabelSign label s 0
  let q := !eightEightLabelSign label s 8
  let ix := label.toEquiv x
  let iy := label.toEquiv y
  have halignx : eightEightAlignedVertexEquiv label s x =
      eightEightParityShift p q ix := rfl
  have haligny : eightEightAlignedVertexEquiv label s y =
      eightEightParityShift p q iy := rfl
  rw [hmodel]
  by_cases hshore : ix.val / 8 = iy.val / 8
  · rw [if_pos hshore, halignx, haligny,
      eightEightParityShift_preserves_lowExterior_within p q ix iy hshore]
  · rw [if_neg hshore, halignx, haligny,
      eightEightLowExteriorPairGraph_adj_iff]
    have hshiftShore :
        (eightEightParityShift p q ix).val / 8 ≠
          (eightEightParityShift p q iy).val / 8 := by
      exact fun h => hshore
        ((eightEightParityShift_sameShore_iff p q ix iy).mp h)
    have hparity := eightEightAlignedVertexEquiv_sign_ne_iff_parity_ne
      H label s hsign hflip x y
    rw [halignx, haligny] at hparity
    constructor
    · intro hs
      exact Or.inr ⟨hshiftShore, hparity.mp hs⟩
    · rintro (⟨hsame, _⟩ | ⟨_, hp⟩)
      · exact (hshiftShore hsame).elim
      · exact hparity.mpr hp

end

end Erdos85

#print axioms Erdos85.eightEightLowExteriorPair_model_of_cycleLabeling
