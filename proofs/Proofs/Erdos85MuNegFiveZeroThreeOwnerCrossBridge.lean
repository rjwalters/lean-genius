import Proofs.Erdos85MuNegFiveZeroThreeOwnerBridge
import Proofs.Erdos85EightEightHighOwnerCnfBridgeCounting

/-!
# Structural cross-clause bridge for h503

The first increment discharges the complete intertwining truth table from the
entrywise C8 balance equation.  It is independent of the eventual graph
coordinate realization.
-/

namespace Erdos85

open Std Sat

theorem muNegFiveZeroThreeCrossIndex?_some_pos
    {x y id : Nat} (h : muNegFiveZeroThreeCrossIndex? x y = some id) :
    0 < id := by
  simp only [muNegFiveZeroThreeCrossIndex?] at h
  split at h
  · obtain ⟨k, _, rfl⟩ := Option.map_eq_some_iff.mp h
    omega
  · contradiction

/-- Every forbidden four-bit mask is excluded when the actual cross-owner
matrix commutes with the two C8 adjacency operators. -/
theorem muNegFiveZeroThreeIntertwiningClauses_satisfied
    (val : DimacsValuation)
    (hbalance : ∀ x y a b c d,
      muNegFiveZeroThreeCrossIndex? ((x + 7) % 8) y = some a →
      muNegFiveZeroThreeCrossIndex? ((x + 1) % 8) y = some b →
      muNegFiveZeroThreeCrossIndex? x ((y + 1) % 8) = some c →
      muNegFiveZeroThreeCrossIndex? x ((y + 7) % 8) = some d →
      (val a).toNat + (val b).toNat =
        (val c).toNat + (val d).toNat) :
    ∀ clause ∈ muNegFiveZeroThreeIntertwiningClauses,
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [muNegFiveZeroThreeIntertwiningClauses, List.mem_flatMap,
    List.mem_range] at hclause
  obtain ⟨x, hx, y, hy, hclause⟩ := hclause
  generalize ha : muNegFiveZeroThreeCrossIndex? ((x + 7) % 8) y = oa
    at hclause
  generalize hb : muNegFiveZeroThreeCrossIndex? ((x + 1) % 8) y = ob
    at hclause
  generalize hc : muNegFiveZeroThreeCrossIndex? x ((y + 1) % 8) = oc
    at hclause
  generalize hd : muNegFiveZeroThreeCrossIndex? x ((y + 7) % 8) = od
    at hclause
  cases oa <;> cases ob <;> cases oc <;> cases od <;>
    simp at hclause
  rename_i a b c d
  obtain ⟨mask, hmask, hclause⟩ := hclause
  obtain ⟨hbad, hclause⟩ := hclause
  subst clause
  simpa using
    dimacsIntertwiningMaskClauseSatisfied_of_balance val a b c d
      (muNegFiveZeroThreeCrossIndex?_some_pos ha)
      (muNegFiveZeroThreeCrossIndex?_some_pos hb)
      (muNegFiveZeroThreeCrossIndex?_some_pos hc)
      (muNegFiveZeroThreeCrossIndex?_some_pos hd)
      (muNegFiveZeroThreeBit mask 3) (muNegFiveZeroThreeBit mask 2)
      (muNegFiveZeroThreeBit mask 1) (muNegFiveZeroThreeBit mask 0)
      hbad (hbalance x y a b c d ha hb hc hd)

def muNegFiveZeroThreeFiberBit
    (val : DimacsValuation) (left : Bool) (z : Nat) (w : Fin 8) : Bool :=
  let x := if left then z else w.val
  let y := if left then w.val else z
  match muNegFiveZeroThreeCrossIndex? x y with
  | some id => val id
  | none => false

def muNegFiveZeroThreeFiberBitsAllowed
    (sigma left : Bool) (z : Nat) (bits : Fin 8 → Bool) : Bool :=
  let total := (List.ofFn bits |>.map Bool.toNat).sum
  let same := ((List.finRange 8).filter fun w =>
    let x := if left then z else w.val
    let y := if left then w.val else z
    muNegFiveZeroThreeSameSign sigma x y).foldl
      (fun n w => n + (bits w).toNat) 0
  total == 5 && same == 3

/-- Finite eight-bit kernel behind the forbidden-mask encoding. -/
theorem muNegFiveZeroThree_forbiddenMask_has_satisfied_bit
    (sigma left : Bool) (z : Fin 8) (mask : Fin 256)
    (bits : Fin 8 → Bool)
    (hallowed : muNegFiveZeroThreeFiberBitsAllowed sigma left z bits = true)
    (hbad : muNegFiveZeroThreeFiberAllowed sigma left z mask = false) :
    ∃ w : Fin 8,
      if muNegFiveZeroThreeBit mask w then bits w = false
      else bits w = true := by
  revert sigma left z mask bits
  native_decide

theorem muNegFiveZeroThreeCrossFiber_zipIdx
    (left : Bool) (z w : Fin 8) :
    ∃ id,
      muNegFiveZeroThreeCrossIndex?
        (if left then z.val else w.val) (if left then w.val else z.val) =
          some id ∧
      (id, w.val) ∈
        (muNegFiveZeroThreeCrossFiber left z.val).zipIdx := by
  revert left z w
  native_decide

theorem muNegFiveZeroThreeCrossDegreeClauses_satisfied
    (sigma : Bool) (val : DimacsValuation)
    (hallowed : ∀ left z, z < 8 →
      muNegFiveZeroThreeFiberBitsAllowed sigma left z
        (muNegFiveZeroThreeFiberBit val left z) = true) :
    ∀ clause ∈ muNegFiveZeroThreeCrossDegreeClauses sigma,
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [muNegFiveZeroThreeCrossDegreeClauses, List.mem_flatMap,
    List.mem_range, List.mem_filterMap] at hclause
  obtain ⟨side, hside, z, hz, mask, hmask, hclause⟩ := hclause
  split at hclause
  · simp at hclause
  · next hforbidden =>
    simp only [Option.some.injEq] at hclause
    subst clause
    have hz8 : z < 8 := hz
    have hmask256 : mask < 256 := hmask
    let left := side == 0
    obtain ⟨w, hw⟩ :=
      muNegFiveZeroThree_forbiddenMask_has_satisfied_bit sigma left
        ⟨z, hz8⟩ ⟨mask, hmask256⟩
        (muNegFiveZeroThreeFiberBit val left z)
        (hallowed left z hz8) (by
          exact Bool.eq_false_iff.mpr hforbidden)
    obtain ⟨id, hidx, hzip⟩ :=
      muNegFiveZeroThreeCrossFiber_zipIdx left ⟨z, hz8⟩ w
    let lit : Int :=
      if muNegFiveZeroThreeBit mask w then -Int.ofNat id else Int.ofNat id
    refine ⟨lit, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨(id, w.val), hzip, by simp [lit]⟩
    · have hid : 0 < id := muNegFiveZeroThreeCrossIndex?_some_pos hidx
      dsimp [lit]
      have hdecode : muNegFiveZeroThreeFiberBit val left z w = val id := by
        simp [muNegFiveZeroThreeFiberBit, hidx]
      by_cases hbit : muNegFiveZeroThreeBit mask w = true
      · have hfalse : val id = false := by
          simpa [hbit, hdecode] using hw
        simp [hbit, dimacsLitValue, hfalse]
      · have hbitFalse : muNegFiveZeroThreeBit mask w = false :=
          Bool.eq_false_of_not_eq_true hbit
        have htrue : val id = true := by
          simpa [hbitFalse, hdecode] using hw
        simp [hbitFalse, dimacsLitValue, hid, htrue]

end Erdos85

#print axioms Erdos85.muNegFiveZeroThreeIntertwiningClauses_satisfied
#print axioms Erdos85.muNegFiveZeroThree_forbiddenMask_has_satisfied_bit
#print axioms Erdos85.muNegFiveZeroThreeCrossDegreeClauses_satisfied
