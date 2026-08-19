import Proofs.Erdos85EightEightHighOwnerCnfBridgeCounting
import Proofs.Erdos85EightEightHighOwnerCnfBridge

/-! # Cross-block clause adapter for the high eight-plus-eight owner CNF -/

namespace Erdos85

open Std Sat

set_option maxHeartbeats 0

def eightEightHighCrossFiberIds (left : Bool) (z : Nat) : Finset Nat :=
  ((eightEightHighCrossFiber left z).map Int.natAbs).toFinset

theorem eightEightHighCrossFiberIds_card_four
    (left : Bool) (z : Nat) (hz : z < 8) :
    (eightEightHighCrossFiberIds left z).card = 4 := by
  interval_cases z <;> cases left <;> native_decide

theorem eightEightHighCrossFiber_id_mem
    (left : Bool) (z : Nat) (lit : Int) (hz : z < 8)
    (hid : lit ∈ eightEightHighCrossFiber left z) :
    lit.natAbs ∈ eightEightHighCrossFiberIds left z := by
  simp only [eightEightHighCrossFiberIds, List.mem_toFinset, List.mem_map]
  exact ⟨lit, hid, rfl⟩

theorem eightEightHighCrossFiber_id_pos
    (left : Bool) (z : Nat) (lit : Int) (hz : z < 8)
    (hid : lit ∈ eightEightHighCrossFiber left z) : 0 < lit := by
  have hall : (eightEightHighCrossFiber left z).all
      (fun x => decide (0 < x)) = true := by
    interval_cases z <;> cases left <;> native_decide
  exact of_decide_eq_true (List.all_eq_true.mp hall lit hid)

/-- Exact-two activity on every cross fiber satisfies all degree clauses
emitted by the generator. -/
theorem eightEightHighCrossDegreeClauses_satisfied
    (val : DimacsValuation)
    (htwo : ∀ left z, z < 8 →
      ((eightEightHighCrossFiberIds left z).filter fun id =>
        val id = true).card = 2) :
    ∀ clause, clause ∈ eightEightHighCrossDegreeClauses →
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [eightEightHighCrossDegreeClauses, List.mem_flatMap,
    List.mem_range, List.mem_filter] at hclause
  obtain ⟨side, hside, z, hz, a, ha, b, ⟨hb, hab⟩,
      c, ⟨hc, hbc⟩, hclause⟩ := hclause
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hclause
  have ha0 := eightEightHighCrossFiber_id_pos (side == 0) z a hz ha
  have hb0 := eightEightHighCrossFiber_id_pos (side == 0) z b hz hb
  have hc0 := eightEightHighCrossFiber_id_pos (side == 0) z c hz hc
  have hab' : a < b := of_decide_eq_true hab
  have hbc' : b < c := of_decide_eq_true hbc
  have habNat : a.natAbs ≠ b.natAbs := by
    intro h
    have hcast := congrArg (fun n : Nat => (n : Int)) h
    exact (_root_.ne_of_lt hab') (by
      simpa [Int.natAbs_of_nonneg ha0.le,
        Int.natAbs_of_nonneg hb0.le] using hcast)
  have hacNat : a.natAbs ≠ c.natAbs := by
    intro h
    have hcast := congrArg (fun n : Nat => (n : Int)) h
    exact (_root_.ne_of_lt (hab'.trans hbc')) (by
      simpa [Int.natAbs_of_nonneg ha0.le,
        Int.natAbs_of_nonneg hc0.le] using hcast)
  have hbcNat : b.natAbs ≠ c.natAbs := by
    intro h
    have hcast := congrArg (fun n : Nat => (n : Int)) h
    exact (_root_.ne_of_lt hbc') (by
      simpa [Int.natAbs_of_nonneg hb0.le,
        Int.natAbs_of_nonneg hc0.le] using hcast)
  have haCast : (a.natAbs : Int) = a := by
    simpa [Int.natCast_natAbs, abs_of_pos ha0]
  have hbCast : (b.natAbs : Int) = b := by
    simpa [Int.natCast_natAbs, abs_of_pos hb0]
  have hcCast : (c.natAbs : Int) = c := by
    simpa [Int.natCast_natAbs, abs_of_pos hc0]
  rcases hclause with rfl | rfl
  · simpa [haCast, hbCast, hcCast] using
      (dimacsTripleClausesSatisfied_of_four_exactly_two_counting val
      (eightEightHighCrossFiberIds (side == 0) z)
      (eightEightHighCrossFiberIds_card_four (side == 0) z hz)
      (htwo (side == 0) z hz)
      (eightEightHighCrossFiber_id_mem (side == 0) z a hz ha)
      (eightEightHighCrossFiber_id_mem (side == 0) z b hz hb)
      (eightEightHighCrossFiber_id_mem (side == 0) z c hz hc)
      (Int.natAbs_pos.mpr (_root_.ne_of_gt ha0))
      (Int.natAbs_pos.mpr (_root_.ne_of_gt hb0))
      (Int.natAbs_pos.mpr (_root_.ne_of_gt hc0))
      habNat hacNat hbcNat).1
  · simpa [haCast, hbCast, hcCast] using
      (dimacsTripleClausesSatisfied_of_four_exactly_two_counting val
      (eightEightHighCrossFiberIds (side == 0) z)
      (eightEightHighCrossFiberIds_card_four (side == 0) z hz)
      (htwo (side == 0) z hz)
      (eightEightHighCrossFiber_id_mem (side == 0) z a hz ha)
      (eightEightHighCrossFiber_id_mem (side == 0) z b hz hb)
      (eightEightHighCrossFiber_id_mem (side == 0) z c hz hc)
      (Int.natAbs_pos.mpr (_root_.ne_of_gt ha0))
      (Int.natAbs_pos.mpr (_root_.ne_of_gt hb0))
      (Int.natAbs_pos.mpr (_root_.ne_of_gt hc0))
      habNat hacNat hbcNat).2

theorem eightEightHighCrossIndex?_some_pos
    {x y id : Nat} (h : eightEightHighCrossIndex? x y = some id) :
    0 < id := by
  simp only [eightEightHighCrossIndex?] at h
  split at h
  · obtain ⟨k, _, rfl⟩ := Option.map_eq_some_iff.mp h
    omega
  · contradiction

/-- The forbidden-mask encoding is sound for any valuation satisfying the
entrywise two-by-two balance recurrence. -/
theorem eightEightHighIntertwiningClauses_satisfied
    (val : DimacsValuation)
    (hbalance : ∀ x y a b c d,
      eightEightHighCrossIndex? ((x + 7) % 8) y = some a →
      eightEightHighCrossIndex? ((x + 1) % 8) y = some b →
      eightEightHighCrossIndex? x ((y + 1) % 8) = some c →
      eightEightHighCrossIndex? x ((y + 7) % 8) = some d →
      (val a).toNat + (val b).toNat = (val c).toNat + (val d).toNat) :
    ∀ clause, clause ∈ eightEightHighIntertwiningClauses →
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [eightEightHighIntertwiningClauses, List.mem_flatMap,
    List.mem_range] at hclause
  obtain ⟨x, hx, y, hy, hclause⟩ := hclause
  generalize ha : eightEightHighCrossIndex? ((x + 7) % 8) y = oa at hclause
  generalize hb : eightEightHighCrossIndex? ((x + 1) % 8) y = ob at hclause
  generalize hc : eightEightHighCrossIndex? x ((y + 1) % 8) = oc at hclause
  generalize hd : eightEightHighCrossIndex? x ((y + 7) % 8) = od at hclause
  cases oa <;> cases ob <;> cases oc <;> cases od <;>
    simp [ha, hb, hc, hd] at hclause
  rename_i a b c d
  obtain ⟨mask, hmask, hclause⟩ := hclause
  obtain ⟨hbad, hclause⟩ := hclause
  subst clause
  simpa using
    dimacsIntertwiningMaskClauseSatisfied_of_balance val a b c d
      (eightEightHighCrossIndex?_some_pos ha)
      (eightEightHighCrossIndex?_some_pos hb)
      (eightEightHighCrossIndex?_some_pos hc)
      (eightEightHighCrossIndex?_some_pos hd)
      (eightEightHighBit mask 3) (eightEightHighBit mask 2)
      (eightEightHighBit mask 1) (eightEightHighBit mask 0)
      hbad (hbalance x y a b c d ha hb hc hd)

theorem eightEightHighHitVariable?_some_of_mem
    {e f : Nat} (hmem : (e, f) ∈ eightEightHighHitVariables) :
    e < 64 ∧ f < 64 ∧ ∃ id, eightEightHighHitVariable? e f = some id := by
  have hbounds : e < 64 ∧ f < 64 := by
    simp only [eightEightHighHitVariables, List.mem_flatMap,
      List.mem_range, List.mem_map, List.mem_filter] at hmem
    obtain ⟨e', he', f', ⟨hf', hcond⟩, hp⟩ := hmem
    have heq : e' = e := congrArg Prod.fst hp
    have hfeq : f' = f := congrArg Prod.snd hp
    omega
  have hef : e < f := by
    simp only [eightEightHighHitVariables, List.mem_flatMap,
      List.mem_range, List.mem_map, List.mem_filter] at hmem
    obtain ⟨e', _, f', ⟨_, hcond⟩, hp⟩ := hmem
    have hef' : e' < f' := by
      simp at hcond
      exact hcond.1
    have heq : e' = e := congrArg Prod.fst hp
    have hfeq : f' = f := congrArg Prod.snd hp
    omega
  have hsome : (eightEightHighHitVariables.idxOf? (e, f)).isSome := by
    simpa using hmem
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨hbounds.1, hbounds.2, i + 33, ?_⟩
  simp [eightEightHighHitVariable?, hef, hi]

/-- Every encoded hit implies activity of each endpoint, so the negative-hit
guards emitted by the generator are satisfied. -/
theorem eightEightHighHitActivityClauses_satisfied
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    (hsymm : ∀ e f, X e f → X f e)
    (hends : ∀ e f, X e f → active e ∧ active f) :
    ∀ clause, clause ∈ eightEightHighHitActivityClauses →
      dimacsClauseSatisfied
        (eightEightHighOwnerValOfRelations active X) clause := by
  intro clause hclause
  simp only [eightEightHighHitActivityClauses, List.mem_flatMap] at hclause
  obtain ⟨p, hp, hclause⟩ := hclause
  rcases p with ⟨e, f⟩
  obtain ⟨he, hf, hitId, hhit⟩ :=
    eightEightHighHitVariable?_some_of_mem hp
  let ef : Fin 64 := ⟨e, he⟩
  let ff : Fin 64 := ⟨f, hf⟩
  have hhitFin : eightEightHighHitVariable? ef ff = some hitId := by
    simpa [ef, ff] using hhit
  simp only [hhit, Option.getD_some] at hclause
  have hsatisfy (q : Fin 64) (activeId : Nat)
      (hactiveVar : eightEightHighActiveVariable? q = some activeId)
      (hendpoint : ∀ hX : X ef ff, active q) :
      dimacsClauseSatisfied (eightEightHighOwnerValOfRelations active X)
        [-Int.ofNat hitId, Int.ofNat activeId] := by
    by_cases hval :
        eightEightHighOwnerValOfRelations active X hitId = true
    · have hX := eightEightHighOwnerRelation_of_val_true active X hsymm
          hhitFin hval
      refine ⟨Int.ofNat activeId, by simp, ?_⟩
      have haval := eightEightHighOwnerVal_active_true_of active X
        hactiveVar (hendpoint hX)
      simp [dimacsLitValue,
        (eightEightHighActiveVariable?_bounds hactiveVar).1, haval]
    · refine ⟨-Int.ofNat hitId, by simp, ?_⟩
      have hfalse : eightEightHighOwnerValOfRelations active X hitId = false :=
        Bool.eq_false_of_not_eq_true hval
      simp [dimacsLitValue,
        (eightEightHighHitVariable?_above_active hhitFin).ne', hfalse]
  generalize hea : eightEightHighActiveVariable? e = oe at hclause
  generalize hfa : eightEightHighActiveVariable? f = of_ at hclause
  cases oe with
  | none =>
      cases of_ with
      | none => simp [hea, hfa] at hclause
      | some b =>
          simp [hea, hfa] at hclause
          subst clause
          exact hsatisfy ff b (by simpa [ff] using hfa)
            (fun hX ↦ (hends ef ff hX).2)
  | some a =>
      cases of_ with
      | none =>
          simp [hea, hfa] at hclause
          subst clause
          exact hsatisfy ef a (by simpa [ef] using hea)
            (fun hX ↦ (hends ef ff hX).1)
      | some b =>
          simp [hea, hfa] at hclause
          rcases hclause with rfl | rfl
          · exact hsatisfy ef a (by simpa [ef] using hea)
              (fun hX ↦ (hends ef ff hX).1)
          · exact hsatisfy ff b (by simpa [ff] using hfa)
              (fun hX ↦ (hends ef ff hX).2)

end Erdos85

#print axioms Erdos85.eightEightHighCrossDegreeClauses_satisfied
#print axioms Erdos85.eightEightHighIntertwiningClauses_satisfied
#print axioms Erdos85.eightEightHighHitActivityClauses_satisfied
