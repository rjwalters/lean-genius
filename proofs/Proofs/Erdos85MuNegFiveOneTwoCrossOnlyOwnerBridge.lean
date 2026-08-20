import Proofs.Erdos85MuNegFiveOneTwoCrossOnlyOwnerCnfSemantics

/-! # Relation valuation for the corrected cross-only h512 owner CNF -/

namespace Erdos85

open Std Sat

set_option maxHeartbeats 0

def muNegFiveOneTwoCrossOnlyOwnerValOfRelations
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X] : DimacsValuation :=
  fun id ↦ if id ≤ 64 then
    decide (∃ e : Fin 64,
      muNegFiveOneTwoCrossOnlyActiveVariable? e = some id ∧ active e)
  else
    decide (∃ e f : Fin 64,
      muNegFiveOneTwoCrossOnlyHitVariable? e f = some id ∧ X e f)

theorem muNegFiveOneTwoCrossOnlyActiveVariable?_bounds
    {e : Fin 64} {id : Nat}
    (h : muNegFiveOneTwoCrossOnlyActiveVariable? e = some id) :
    0 < id ∧ id ≤ 64 := by
  revert e id
  native_decide

theorem muNegFiveOneTwoCrossOnlyHitVariable?_above_active
    {e f : Fin 64} {id : Nat}
    (h : muNegFiveOneTwoCrossOnlyHitVariable? e f = some id) : 64 < id := by
  revert e f id
  native_decide

theorem muNegFiveOneTwoCrossOnlyOwnerVal_active_true_iff
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    {id : Nat} (hid : id ≤ 64) :
    muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X id = true ↔
      ∃ e : Fin 64,
        muNegFiveOneTwoCrossOnlyActiveVariable? e = some id ∧ active e := by
  simp [muNegFiveOneTwoCrossOnlyOwnerValOfRelations, hid]

theorem muNegFiveOneTwoCrossOnlyOwnerVal_hit_true_iff
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    {id : Nat} (hid : 64 < id) :
    muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X id = true ↔
      ∃ e f : Fin 64,
        muNegFiveOneTwoCrossOnlyHitVariable? e f = some id ∧ X e f := by
  simp [muNegFiveOneTwoCrossOnlyOwnerValOfRelations, Nat.not_le.mpr hid]

theorem muNegFiveOneTwoCrossOnlyActiveVariable?_eq_injective
    (e f : Fin 64) {id : Nat}
    (he : muNegFiveOneTwoCrossOnlyActiveVariable? e = some id)
    (hf : muNegFiveOneTwoCrossOnlyActiveVariable? f = some id) : e = f := by
  revert e f id
  native_decide

theorem muNegFiveOneTwoCrossOnlyHitVariable?_eq_injective
    (e f a b : Fin 64) {id : Nat}
    (hef : muNegFiveOneTwoCrossOnlyHitVariable? e f = some id)
    (hab : muNegFiveOneTwoCrossOnlyHitVariable? a b = some id) :
    (e = a ∧ f = b) ∨ (e = b ∧ f = a) := by
  let p : Nat × Nat :=
    if e.val < f.val then (e.val, f.val) else (f.val, e.val)
  let q : Nat × Nat :=
    if a.val < b.val then (a.val, b.val) else (b.val, a.val)
  change (muNegFiveOneTwoCrossOnlyHitVariables.idxOf? p).map (· + 65) =
    some id at hef
  change (muNegFiveOneTwoCrossOnlyHitVariables.idxOf? q).map (· + 65) =
    some id at hab
  have heqIdx : muNegFiveOneTwoCrossOnlyHitVariables.idxOf? p =
      muNegFiveOneTwoCrossOnlyHitVariables.idxOf? q := by
    exact Option.map_injective (f := fun n : Nat ↦ n + 65)
      (fun _ _ h ↦ Nat.add_right_cancel h) (hef.trans hab.symm)
  cases hp : muNegFiveOneTwoCrossOnlyHitVariables.idxOf? p with
  | none => simp [hp] at hef
  | some i =>
      have hq : muNegFiveOneTwoCrossOnlyHitVariables.idxOf? q = some i := by
        rw [← heqIdx, hp]
      obtain ⟨_, hgetp, _⟩ := List.idxOf?_eq_some_iff.mp hp
      obtain ⟨_, hgetq, _⟩ := List.idxOf?_eq_some_iff.mp hq
      have hpq : p = q := hgetp.symm.trans hgetq
      dsimp [p, q] at hpq
      split at hpq <;> split at hpq
      <;> simp only [Prod.mk.injEq] at hpq
      <;> omega

theorem muNegFiveOneTwoCrossOnlyOwnerVal_active_true_of
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    {e : Fin 64} {id : Nat}
    (hvar : muNegFiveOneTwoCrossOnlyActiveVariable? e = some id)
    (hactive : active e) :
    muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X id = true := by
  exact (muNegFiveOneTwoCrossOnlyOwnerVal_active_true_iff active X
    (muNegFiveOneTwoCrossOnlyActiveVariable?_bounds hvar).2).mpr
      ⟨e, hvar, hactive⟩

theorem muNegFiveOneTwoCrossOnlyOwnerVal_hit_true_of
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    {e f : Fin 64} {id : Nat}
    (hvar : muNegFiveOneTwoCrossOnlyHitVariable? e f = some id)
    (hX : X e f) :
    muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X id = true := by
  exact (muNegFiveOneTwoCrossOnlyOwnerVal_hit_true_iff active X
    (muNegFiveOneTwoCrossOnlyHitVariable?_above_active hvar)).mpr
      ⟨e, f, hvar, hX⟩

theorem muNegFiveOneTwoCrossOnlyOwnerActive_of_val_true
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    {e : Fin 64} {id : Nat}
    (hvar : muNegFiveOneTwoCrossOnlyActiveVariable? e = some id)
    (hval : muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X id = true) :
    active e := by
  obtain ⟨f, hfvar, hf⟩ :=
    (muNegFiveOneTwoCrossOnlyOwnerVal_active_true_iff active X
      (muNegFiveOneTwoCrossOnlyActiveVariable?_bounds hvar).2).mp hval
  rw [muNegFiveOneTwoCrossOnlyActiveVariable?_eq_injective e f hvar hfvar]
  exact hf

theorem muNegFiveOneTwoCrossOnlyOwnerRelation_of_val_true
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsymm : ∀ e f, X e f → X f e)
    {e f : Fin 64} {id : Nat}
    (hvar : muNegFiveOneTwoCrossOnlyHitVariable? e f = some id)
    (hval : muNegFiveOneTwoCrossOnlyOwnerValOfRelations active X id = true) :
    X e f := by
  obtain ⟨a, b, hab, hX⟩ :=
    (muNegFiveOneTwoCrossOnlyOwnerVal_hit_true_iff active X
      (muNegFiveOneTwoCrossOnlyHitVariable?_above_active hvar)).mp hval
  rcases muNegFiveOneTwoCrossOnlyHitVariable?_eq_injective
      e f a b hvar hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hX
  · exact hsymm _ _ hX

end Erdos85

#print axioms Erdos85.muNegFiveOneTwoCrossOnlyActiveVariable?_bounds
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyHitVariable?_above_active
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyActiveVariable?_eq_injective
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyHitVariable?_eq_injective
