import Proofs.Erdos85EightEightHighOwnerOutsideTransport

/-! # Coordinate transport for the high-owner cross clauses -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

def eightEightHighCrossFiberX (left : Bool) (z w : Fin 8) : Fin 8 :=
  if left == true then z else w

def eightEightHighCrossFiberY (left : Bool) (z w : Fin 8) : Fin 8 :=
  if left == true then w else z

theorem eightEightHighCrossIndex_some_parity
    {x y id : Nat} (h : eightEightHighCrossIndex? x y = some id) :
    x % 2 ≠ y % 2 := by
  unfold eightEightHighCrossIndex? at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    exact bne_iff_ne.mp hcond.2
  · contradiction

theorem eightEightHighCrossIndex_some_bounds
    {x y id : Nat} (h : eightEightHighCrossIndex? x y = some id) :
    x < 8 ∧ y < 8 := by
  unfold eightEightHighCrossIndex? at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    exact hcond.1
  · contradiction

def eightEightHighCrossFiberId (left : Bool) (z w : Fin 8) : Nat :=
  (eightEightHighCrossIndex?
    (eightEightHighCrossFiberX left z w)
    (eightEightHighCrossFiberY left z w)).getD 0

theorem eightEightHighCrossFiberId_spec
    (left : Bool) (z w : Fin 8)
    (hpar : (eightEightHighCrossFiberX left z w).val % 2 ≠
      (eightEightHighCrossFiberY left z w).val % 2) :
    eightEightHighCrossIndex?
        (eightEightHighCrossFiberX left z w)
        (eightEightHighCrossFiberY left z w) =
      some (eightEightHighCrossFiberId left z w) := by
  revert left z w
  native_decide

theorem eightEightHighCrossFiberId_injective_on_candidates
    (left : Bool) (z w₁ w₂ : Fin 8)
    (h₁ : (eightEightHighCrossFiberX left z w₁).val % 2 ≠
      (eightEightHighCrossFiberY left z w₁).val % 2)
    (h₂ : (eightEightHighCrossFiberX left z w₂).val % 2 ≠
      (eightEightHighCrossFiberY left z w₂).val % 2)
    (hid : eightEightHighCrossFiberId left z w₁ =
      eightEightHighCrossFiberId left z w₂) : w₁ = w₂ := by
  revert left z w₁ w₂
  native_decide

theorem eightEightHighCrossFiberId_mem
    (left : Bool) (z w : Fin 8)
    (hpar : (eightEightHighCrossFiberX left z w).val % 2 ≠
      (eightEightHighCrossFiberY left z w).val % 2) :
    eightEightHighCrossFiberId left z w ∈
      eightEightHighCrossFiberIds left z := by
  have hspec := eightEightHighCrossFiberId_spec left z w hpar
  simp only [eightEightHighCrossFiberIds, List.mem_toFinset, List.mem_map,
    eightEightHighCrossFiber, List.mem_filterMap, List.mem_range]
  refine ⟨Int.ofNat (eightEightHighCrossFiberId left z w), ?_, by simp⟩
  refine ⟨w.val, w.2, ?_⟩
  cases left <;>
    simpa [eightEightHighCrossFiberX, eightEightHighCrossFiberY] using hspec

theorem eightEightHighCrossFiberId_surjective
    (left : Bool) (z : Fin 8) (id : Nat)
    (hid : id ∈ eightEightHighCrossFiberIds left z) :
    ∃ w : Fin 8,
      (eightEightHighCrossFiberX left z w).val % 2 ≠
        (eightEightHighCrossFiberY left z w).val % 2 ∧
      eightEightHighCrossFiberId left z w = id := by
  simp only [eightEightHighCrossFiberIds, List.mem_toFinset, List.mem_map,
    eightEightHighCrossFiber, List.mem_filterMap, List.mem_range] at hid
  obtain ⟨lit, ⟨w, hw8, hw⟩, hlit⟩ := hid
  let wf : Fin 8 := ⟨w, hw8⟩
  simp only [Option.map_eq_some_iff] at hw
  obtain ⟨raw, hraw, rfl⟩ := hw
  have hpar : (eightEightHighCrossFiberX left z wf).val % 2 ≠
      (eightEightHighCrossFiberY left z wf).val % 2 := by
    have hp := eightEightHighCrossIndex_some_parity hraw
    cases left <;>
      simpa [eightEightHighCrossFiberX, eightEightHighCrossFiberY, wf] using hp
  refine ⟨wf, hpar, ?_⟩
  have hspec := eightEightHighCrossFiberId_spec left z wf hpar
  have hraw' : eightEightHighCrossIndex?
      (eightEightHighCrossFiberX left z wf)
      (eightEightHighCrossFiberY left z wf) = some raw := by
    cases left <;>
      simpa [eightEightHighCrossFiberX, eightEightHighCrossFiberY, wf] using hraw
  rw [hraw'] at hspec
  simp at hspec
  have hrawid : raw = id := by simpa using hlit
  exact hspec.symm.trans hrawid

/-- Exact row/column degree two in the coordinate exterior graph is exactly
the filtered DIMACS activity count used by the high-owner terminal. -/
theorem eightEightHighOwner_crossFiber_two_of_coordinate_degrees
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (X : Fin 64 → Fin 64 → Prop) [DecidableRel X]
    (hrow : ∀ x : Fin 8,
      ((Finset.univ : Finset (Fin 8)).filter fun y =>
        x.val % 2 ≠ y.val % 2 ∧
          R.Adj ⟨x.val, by omega⟩ ⟨8 + y.val, by omega⟩).card = 2)
    (hcol : ∀ y : Fin 8,
      ((Finset.univ : Finset (Fin 8)).filter fun x =>
        x.val % 2 ≠ y.val % 2 ∧
          R.Adj ⟨x.val, by omega⟩ ⟨8 + y.val, by omega⟩).card = 2) :
    ∀ left z, z < 8 →
      ((eightEightHighCrossFiberIds left z).filter fun id =>
        eightEightHighOwnerValOfRelations
          (eightEightHighCoordinateActive R) X id = true).card = 2 := by
  intro left z hz
  let zf : Fin 8 := ⟨z, hz⟩
  let S := (Finset.univ : Finset (Fin 8)).filter fun w =>
    (eightEightHighCrossFiberX left zf w).val % 2 ≠
      (eightEightHighCrossFiberY left zf w).val % 2 ∧
    R.Adj
      ⟨(eightEightHighCrossFiberX left zf w).val, by omega⟩
      ⟨8 + (eightEightHighCrossFiberY left zf w).val, by omega⟩
  let T := (eightEightHighCrossFiberIds left z).filter fun id =>
    eightEightHighOwnerValOfRelations
      (eightEightHighCoordinateActive R) X id = true
  have hScard : S.card = 2 := by
    cases left with
    | false => simpa [S, eightEightHighCrossFiberX,
        eightEightHighCrossFiberY, zf] using hcol zf
    | true => simpa [S, eightEightHighCrossFiberX,
        eightEightHighCrossFiberY, zf] using hrow zf
  have hcard : S.card = T.card := by
    apply Finset.card_bij
      (fun w _ ↦ eightEightHighCrossFiberId left zf w)
    · intro w hw
      have hw' := Finset.mem_filter.mp hw
      apply Finset.mem_filter.mpr
      refine ⟨eightEightHighCrossFiberId_mem left zf w hw'.2.1, ?_⟩
      exact (eightEightHighOwnerVal_crossIndex_coordinate_iff R X
        (eightEightHighCrossFiberX left zf w).2
        (eightEightHighCrossFiberY left zf w).2
        (eightEightHighCrossFiberId_spec left zf w hw'.2.1)).mpr hw'.2.2
    · intro w₁ hw₁ w₂ hw₂ heq
      exact eightEightHighCrossFiberId_injective_on_candidates
        left zf w₁ w₂ (Finset.mem_filter.mp hw₁).2.1
          (Finset.mem_filter.mp hw₂).2.1 heq
    · intro id hid
      have hid' := Finset.mem_filter.mp hid
      obtain ⟨w, hpar, hwid⟩ :=
        eightEightHighCrossFiberId_surjective left zf id hid'.1
      have hR := (eightEightHighOwnerVal_crossIndex_coordinate_iff R X
        (eightEightHighCrossFiberX left zf w).2
        (eightEightHighCrossFiberY left zf w).2
        (eightEightHighCrossFiberId_spec left zf w hpar)).mp (by
          simpa [hwid] using hid'.2)
      refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpar, hR⟩, hwid⟩
  exact hcard ▸ hScard

/-- The coordinate exterior recurrence is exactly the Boolean balance law
consumed by the high-owner intertwining clauses. -/
theorem eightEightHighOwner_balance_of_coordinate_balance
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (X : Fin 64 → Fin 64 → Prop) [DecidableRel X]
    (hR : ∀ x y : Nat, ∀ (hx : x < 8) (hy : y < 8),
      (decide (R.Adj ⟨(x + 7) % 8, by omega⟩
        ⟨8 + y, by omega⟩)).toNat +
          (decide (R.Adj ⟨(x + 1) % 8, by omega⟩
            ⟨8 + y, by omega⟩)).toNat =
        (decide (R.Adj ⟨x, by omega⟩
          ⟨8 + (y + 1) % 8, by omega⟩)).toNat +
          (decide (R.Adj ⟨x, by omega⟩
            ⟨8 + (y + 7) % 8, by omega⟩)).toNat) :
    ∀ x y a b c d,
      eightEightHighCrossIndex? ((x + 7) % 8) y = some a →
      eightEightHighCrossIndex? ((x + 1) % 8) y = some b →
      eightEightHighCrossIndex? x ((y + 1) % 8) = some c →
      eightEightHighCrossIndex? x ((y + 7) % 8) = some d →
      (eightEightHighOwnerValOfRelations
          (eightEightHighCoordinateActive R) X a).toNat +
          (eightEightHighOwnerValOfRelations
            (eightEightHighCoordinateActive R) X b).toNat =
        (eightEightHighOwnerValOfRelations
          (eightEightHighCoordinateActive R) X c).toNat +
          (eightEightHighOwnerValOfRelations
            (eightEightHighCoordinateActive R) X d).toNat := by
  intro x y a b c d ha hb hc hd
  have hy : y < 8 := (eightEightHighCrossIndex_some_bounds ha).2
  have hx : x < 8 := (eightEightHighCrossIndex_some_bounds hc).1
  have hva : eightEightHighOwnerValOfRelations
      (eightEightHighCoordinateActive R) X a =
      decide (R.Adj ⟨(x + 7) % 8, by omega⟩ ⟨8 + y, by omega⟩) := by
    apply Bool.eq_iff_iff.mpr
    rw [eightEightHighOwnerVal_crossIndex_coordinate_iff R X
      (by omega) hy ha, decide_eq_true_eq]
  have hvb : eightEightHighOwnerValOfRelations
      (eightEightHighCoordinateActive R) X b =
      decide (R.Adj ⟨(x + 1) % 8, by omega⟩ ⟨8 + y, by omega⟩) := by
    apply Bool.eq_iff_iff.mpr
    rw [eightEightHighOwnerVal_crossIndex_coordinate_iff R X
      (by omega) hy hb, decide_eq_true_eq]
  have hvc : eightEightHighOwnerValOfRelations
      (eightEightHighCoordinateActive R) X c =
      decide (R.Adj ⟨x, by omega⟩ ⟨8 + (y + 1) % 8, by omega⟩) := by
    apply Bool.eq_iff_iff.mpr
    rw [eightEightHighOwnerVal_crossIndex_coordinate_iff R X
      hx (by omega) hc, decide_eq_true_eq]
  have hvd : eightEightHighOwnerValOfRelations
      (eightEightHighCoordinateActive R) X d =
      decide (R.Adj ⟨x, by omega⟩ ⟨8 + (y + 7) % 8, by omega⟩) := by
    apply Bool.eq_iff_iff.mpr
    rw [eightEightHighOwnerVal_crossIndex_coordinate_iff R X
      hx (by omega) hd, decide_eq_true_eq]
  rw [hva, hvb, hvc, hvd]
  exact hR x y hx hy

end

end Erdos85

#print axioms Erdos85.eightEightHighOwner_crossFiber_two_of_coordinate_degrees
#print axioms Erdos85.eightEightHighOwner_balance_of_coordinate_balance
