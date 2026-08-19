import Proofs.Erdos85EightEightHighOwnerCnfBridgeCounting

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

end Erdos85

#print axioms Erdos85.eightEightHighCrossDegreeClauses_satisfied
