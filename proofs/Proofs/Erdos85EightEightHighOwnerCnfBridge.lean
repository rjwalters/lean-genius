import Proofs.Erdos85EightEightHighOwnerCnfSemantics
import Proofs.Erdos85EightEightLowOwnerCnfBridge

/-!
# Finite-relation bridge for the variable-cross high eight-plus-eight CNF

The high owner instance has two disjoint variable bands: variables `1..32`
select the cross exterior-pair edges, while variables from `33` onward encode
adjacency between selected exterior pairs.  This file isolates that decoding
from the graph-facing coordinate argument.
-/

namespace Erdos85

open Std Sat

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Truth assignment induced by a candidate-activity predicate and an owner
adjacency relation.  Splitting at variable 32 makes the two generator bands
definitionally disjoint. -/
def eightEightHighOwnerValOfRelations
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X] : DimacsValuation :=
  fun id ↦ if id ≤ 32 then
    decide (∃ e : Fin 64,
      eightEightHighActiveVariable? e = some id ∧ active e)
  else
    decide (∃ e f : Fin 64,
      eightEightHighHitVariable? e f = some id ∧ X e f)

/-- Every generated activity identifier lies in the first variable band. -/
theorem eightEightHighActiveVariable?_bounds
    {e : Fin 64} {id : Nat}
    (h : eightEightHighActiveVariable? e = some id) :
    0 < id ∧ id ≤ 32 := by
  revert e id
  native_decide

/-- Every generated hit identifier lies strictly above the activity band. -/
theorem eightEightHighHitVariable?_above_active
    {e f : Fin 64} {id : Nat}
    (h : eightEightHighHitVariable? e f = some id) : 32 < id := by
  revert e f id
  native_decide

theorem eightEightHighOwnerVal_active_true_iff
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    {id : Nat} (hid : id ≤ 32) :
    eightEightHighOwnerValOfRelations active X id = true ↔
      ∃ e : Fin 64,
        eightEightHighActiveVariable? e = some id ∧ active e := by
  simp [eightEightHighOwnerValOfRelations, hid]

theorem eightEightHighOwnerVal_hit_true_iff
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    {id : Nat} (hid : 32 < id) :
    eightEightHighOwnerValOfRelations active X id = true ↔
      ∃ e f : Fin 64,
        eightEightHighHitVariable? e f = some id ∧ X e f := by
  simp [eightEightHighOwnerValOfRelations, Nat.not_le.mpr hid]

theorem eightEightHighOwnerVal_active_true_of
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    {e : Fin 64} {id : Nat}
    (hvar : eightEightHighActiveVariable? e = some id)
    (hactive : active e) :
    eightEightHighOwnerValOfRelations active X id = true := by
  exact (eightEightHighOwnerVal_active_true_iff active X
    (eightEightHighActiveVariable?_bounds hvar).2).mpr
      ⟨e, hvar, hactive⟩

theorem eightEightHighOwnerVal_hit_true_of
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    {e f : Fin 64} {id : Nat}
    (hvar : eightEightHighHitVariable? e f = some id)
    (hX : X e f) :
    eightEightHighOwnerValOfRelations active X id = true := by
  exact (eightEightHighOwnerVal_hit_true_iff active X
    (eightEightHighHitVariable?_above_active hvar)).mpr
      ⟨e, f, hvar, hX⟩

/-- Activity identifiers uniquely determine their candidate owner. -/
theorem eightEightHighActiveVariable?_eq_injective
    (e f : Fin 64) {id : Nat}
    (he : eightEightHighActiveVariable? e = some id)
    (hf : eightEightHighActiveVariable? f = some id) : e = f := by
  revert e f id
  native_decide

/-- Hit identifiers determine the unordered pair of candidate owners. -/
theorem eightEightHighHitVariable?_eq_injective
    (e f a b : Fin 64) {id : Nat}
    (hef : eightEightHighHitVariable? e f = some id)
    (hab : eightEightHighHitVariable? a b = some id) :
    (e = a ∧ f = b) ∨ (e = b ∧ f = a) := by
  let p : Nat × Nat :=
    if e.val < f.val then (e.val, f.val) else (f.val, e.val)
  let q : Nat × Nat :=
    if a.val < b.val then (a.val, b.val) else (b.val, a.val)
  change (eightEightHighHitVariables.idxOf? p).map (· + 33) = some id at hef
  change (eightEightHighHitVariables.idxOf? q).map (· + 33) = some id at hab
  have heqIdx : eightEightHighHitVariables.idxOf? p =
      eightEightHighHitVariables.idxOf? q := by
    exact Option.map_injective (f := fun n : Nat ↦ n + 33)
      (fun _ _ h ↦ Nat.add_right_cancel h) (hef.trans hab.symm)
  cases hp : eightEightHighHitVariables.idxOf? p with
  | none => simp [hp] at hef
  | some i =>
      have hq : eightEightHighHitVariables.idxOf? q = some i := by
        rw [← heqIdx, hp]
      obtain ⟨_, hgetp, _⟩ := List.idxOf?_eq_some_iff.mp hp
      obtain ⟨_, hgetq, _⟩ := List.idxOf?_eq_some_iff.mp hq
      have hpq : p = q := hgetp.symm.trans hgetq
      dsimp [p, q] at hpq
      split at hpq <;> split at hpq
      <;> simp only [Prod.mk.injEq] at hpq
      <;> omega

theorem eightEightHighOwnerActive_of_val_true
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    {e : Fin 64} {id : Nat}
    (hvar : eightEightHighActiveVariable? e = some id)
    (hval : eightEightHighOwnerValOfRelations active X id = true) :
    active e := by
  obtain ⟨f, hfvar, hf⟩ :=
    (eightEightHighOwnerVal_active_true_iff active X
      (eightEightHighActiveVariable?_bounds hvar).2).mp hval
  rw [eightEightHighActiveVariable?_eq_injective e f hvar hfvar]
  exact hf

theorem eightEightHighOwnerRelation_of_val_true
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsymm : ∀ e f, X e f → X f e)
    {e f : Fin 64} {id : Nat}
    (hvar : eightEightHighHitVariable? e f = some id)
    (hval : eightEightHighOwnerValOfRelations active X id = true) :
    X e f := by
  obtain ⟨a, b, hab, hX⟩ :=
    (eightEightHighOwnerVal_hit_true_iff active X
      (eightEightHighHitVariable?_above_active hvar)).mp hval
  rcases eightEightHighHitVariable?_eq_injective e f a b hvar hab with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hX
  · exact hsymm _ _ hX

end Erdos85

#print axioms Erdos85.eightEightHighActiveVariable?_bounds
#print axioms Erdos85.eightEightHighHitVariable?_above_active
#print axioms Erdos85.eightEightHighActiveVariable?_eq_injective
#print axioms Erdos85.eightEightHighHitVariable?_eq_injective
