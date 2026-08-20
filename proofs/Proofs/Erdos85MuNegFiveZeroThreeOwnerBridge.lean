import Proofs.Erdos85MuNegFiveZeroThreeOwnerCnfSemantics

/-!
# Relation valuation for the h503 owner CNF

Variables `1..64` encode activity of the cross-owner candidates.  Variables
from `65` encode adjacency between candidate owner vertices.  This file keeps
that numbering out of the graph-facing layer.
-/

namespace Erdos85

open Std Sat

set_option maxHeartbeats 0

def muNegFiveZeroThreeOwnerValOfRelations
    (active : Fin 72 → Prop) (X : Fin 72 → Fin 72 → Prop)
    [DecidablePred active] [DecidableRel X] : DimacsValuation :=
  fun id => if id ≤ 64 then
    decide (∃ e : Fin 72,
      muNegFiveZeroThreeActiveVariable? e = some id ∧ active e)
  else
    decide (∃ e f : Fin 72,
      muNegFiveZeroThreeHitVariable? e f = some id ∧ X e f)

theorem muNegFiveZeroThreeActiveVariable?_bounds
    {e : Fin 72} {id : Nat}
    (h : muNegFiveZeroThreeActiveVariable? e = some id) :
    0 < id ∧ id ≤ 64 := by
  revert e id
  native_decide

theorem muNegFiveZeroThreeHitVariable?_above_active
    {e f : Fin 72} {id : Nat}
    (h : muNegFiveZeroThreeHitVariable? e f = some id) : 64 < id := by
  revert e f id
  native_decide

theorem muNegFiveZeroThreeOwnerVal_active_true_iff
    (active : Fin 72 → Prop) (X : Fin 72 → Fin 72 → Prop)
    [DecidablePred active] [DecidableRel X]
    {id : Nat} (hid : id ≤ 64) :
    muNegFiveZeroThreeOwnerValOfRelations active X id = true ↔
      ∃ e : Fin 72,
        muNegFiveZeroThreeActiveVariable? e = some id ∧ active e := by
  simp [muNegFiveZeroThreeOwnerValOfRelations, hid]

theorem muNegFiveZeroThreeOwnerVal_hit_true_iff
    (active : Fin 72 → Prop) (X : Fin 72 → Fin 72 → Prop)
    [DecidablePred active] [DecidableRel X]
    {id : Nat} (hid : 64 < id) :
    muNegFiveZeroThreeOwnerValOfRelations active X id = true ↔
      ∃ e f : Fin 72,
        muNegFiveZeroThreeHitVariable? e f = some id ∧ X e f := by
  simp [muNegFiveZeroThreeOwnerValOfRelations, Nat.not_le.mpr hid]

theorem muNegFiveZeroThreeActiveVariable?_eq_injective
    (e f : Fin 72) {id : Nat}
    (he : muNegFiveZeroThreeActiveVariable? e = some id)
    (hf : muNegFiveZeroThreeActiveVariable? f = some id) : e = f := by
  revert e f id
  native_decide

theorem muNegFiveZeroThreeHitVariable?_eq_injective
    (e f a b : Fin 72) {id : Nat}
    (hef : muNegFiveZeroThreeHitVariable? e f = some id)
    (hab : muNegFiveZeroThreeHitVariable? a b = some id) :
    (e = a ∧ f = b) ∨ (e = b ∧ f = a) := by
  let p : Nat × Nat :=
    if e.val < f.val then (e.val, f.val) else (f.val, e.val)
  let q : Nat × Nat :=
    if a.val < b.val then (a.val, b.val) else (b.val, a.val)
  change (muNegFiveZeroThreeHitVariables.idxOf? p).map (· + 65) = some id at hef
  change (muNegFiveZeroThreeHitVariables.idxOf? q).map (· + 65) = some id at hab
  have heqIdx : muNegFiveZeroThreeHitVariables.idxOf? p =
      muNegFiveZeroThreeHitVariables.idxOf? q := by
    exact Option.map_injective (f := fun n : Nat => n + 65)
      (fun _ _ h => Nat.add_right_cancel h) (hef.trans hab.symm)
  cases hp : muNegFiveZeroThreeHitVariables.idxOf? p with
  | none => simp [hp] at hef
  | some i =>
      have hq : muNegFiveZeroThreeHitVariables.idxOf? q = some i := by
        rw [← heqIdx, hp]
      obtain ⟨_, hgetp, _⟩ := List.idxOf?_eq_some_iff.mp hp
      obtain ⟨_, hgetq, _⟩ := List.idxOf?_eq_some_iff.mp hq
      have hpq : p = q := hgetp.symm.trans hgetq
      dsimp [p, q] at hpq
      split at hpq <;> split at hpq
      <;> simp only [Prod.mk.injEq] at hpq
      <;> omega

theorem muNegFiveZeroThreeOwnerVal_active_true_of
    (active : Fin 72 → Prop) (X : Fin 72 → Fin 72 → Prop)
    [DecidablePred active] [DecidableRel X]
    {e : Fin 72} {id : Nat}
    (hvar : muNegFiveZeroThreeActiveVariable? e = some id)
    (hactive : active e) :
    muNegFiveZeroThreeOwnerValOfRelations active X id = true := by
  exact (muNegFiveZeroThreeOwnerVal_active_true_iff active X
    (muNegFiveZeroThreeActiveVariable?_bounds hvar).2).mpr
      ⟨e, hvar, hactive⟩

theorem muNegFiveZeroThreeOwnerVal_hit_true_of
    (active : Fin 72 → Prop) (X : Fin 72 → Fin 72 → Prop)
    [DecidablePred active] [DecidableRel X]
    {e f : Fin 72} {id : Nat}
    (hvar : muNegFiveZeroThreeHitVariable? e f = some id)
    (hX : X e f) :
    muNegFiveZeroThreeOwnerValOfRelations active X id = true := by
  exact (muNegFiveZeroThreeOwnerVal_hit_true_iff active X
    (muNegFiveZeroThreeHitVariable?_above_active hvar)).mpr
      ⟨e, f, hvar, hX⟩

theorem muNegFiveZeroThreeOwnerActive_of_val_true
    (active : Fin 72 → Prop) (X : Fin 72 → Fin 72 → Prop)
    [DecidablePred active] [DecidableRel X]
    {e : Fin 72} {id : Nat}
    (hvar : muNegFiveZeroThreeActiveVariable? e = some id)
    (hval : muNegFiveZeroThreeOwnerValOfRelations active X id = true) :
    active e := by
  obtain ⟨f, hfvar, hf⟩ :=
    (muNegFiveZeroThreeOwnerVal_active_true_iff active X
      (muNegFiveZeroThreeActiveVariable?_bounds hvar).2).mp hval
  rw [muNegFiveZeroThreeActiveVariable?_eq_injective e f hvar hfvar]
  exact hf

theorem muNegFiveZeroThreeOwnerRelation_of_val_true
    (active : Fin 72 → Prop) (X : Fin 72 → Fin 72 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsymm : ∀ e f, X e f → X f e)
    {e f : Fin 72} {id : Nat}
    (hvar : muNegFiveZeroThreeHitVariable? e f = some id)
    (hval : muNegFiveZeroThreeOwnerValOfRelations active X id = true) :
    X e f := by
  obtain ⟨a, b, hab, hX⟩ :=
    (muNegFiveZeroThreeOwnerVal_hit_true_iff active X
      (muNegFiveZeroThreeHitVariable?_above_active hvar)).mp hval
  rcases muNegFiveZeroThreeHitVariable?_eq_injective e f a b hvar hab with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hX
  · exact hsymm _ _ hX

end Erdos85

#print axioms Erdos85.muNegFiveZeroThreeActiveVariable?_bounds
#print axioms Erdos85.muNegFiveZeroThreeHitVariable?_above_active
#print axioms Erdos85.muNegFiveZeroThreeActiveVariable?_eq_injective
#print axioms Erdos85.muNegFiveZeroThreeHitVariable?_eq_injective
