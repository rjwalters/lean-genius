import Proofs.Erdos85MuNegFiveCanonicalOwnerCnfSemantics
import Proofs.Erdos85MuNegFiveZeroThreeOwnerCrossBridge

/-!
# Cross-degree clause bridge for h504 and h512

The cross-index table and literal decoder are shared with h503.  Only the
allowed eight-bit fiber census changes, so one generic embedding proof serves
both remaining endpoints after two small finite kernels.
-/

namespace Erdos85

open Std Sat

def muNegFiveCanonicalFiberBitsAllowed
    (total same : Nat) (sigma left : Bool) (z : Nat)
    (bits : Fin 8 → Bool) : Bool :=
  let actualTotal := (List.ofFn bits |>.map Bool.toNat).sum
  let actualSame := ((List.finRange 8).filter fun w =>
    let x := if left then z else w.val
    let y := if left then w.val else z
    muNegFiveZeroThreeSameSign sigma x y).foldl
      (fun n w => n + (bits w).toNat) 0
  actualTotal == total && actualSame == same

theorem muNegFiveZeroFour_forbiddenMask_has_satisfied_bit
    (sigma left : Bool) (z : Fin 8) (mask : Fin 256)
    (bits : Fin 8 → Bool)
    (hallowed : muNegFiveCanonicalFiberBitsAllowed
      4 3 sigma left z bits = true)
    (hbad : muNegFiveCanonicalFiberAllowed
      4 3 sigma left z mask = false) :
    ∃ w : Fin 8,
      if muNegFiveZeroThreeBit mask w then bits w = false
      else bits w = true := by
  revert sigma left z mask bits
  native_decide

theorem muNegFiveOneTwo_forbiddenMask_has_satisfied_bit
    (sigma left : Bool) (z : Fin 8) (mask : Fin 256)
    (bits : Fin 8 → Bool)
    (hallowed : muNegFiveCanonicalFiberBitsAllowed
      6 4 sigma left z bits = true)
    (hbad : muNegFiveCanonicalFiberAllowed
      6 4 sigma left z mask = false) :
    ∃ w : Fin 8,
      if muNegFiveZeroThreeBit mask w then bits w = false
      else bits w = true := by
  revert sigma left z mask bits
  native_decide

theorem muNegFiveCanonicalCrossDegreeClauses_satisfied
    (total same : Nat) (sigma : Bool) (val : DimacsValuation)
    (hkernel : ∀ (sigma left : Bool) (z : Fin 8) (mask : Fin 256)
      (bits : Fin 8 → Bool),
      muNegFiveCanonicalFiberBitsAllowed
        total same sigma left z bits = true →
      muNegFiveCanonicalFiberAllowed
        total same sigma left z mask = false →
      ∃ w : Fin 8,
        if muNegFiveZeroThreeBit mask w then bits w = false
        else bits w = true)
    (hallowed : ∀ left z, z < 8 →
      muNegFiveCanonicalFiberBitsAllowed total same sigma left z
        (muNegFiveZeroThreeFiberBit val left z) = true) :
    ∀ clause ∈ muNegFiveCanonicalCrossDegreeClauses total same sigma,
      dimacsClauseSatisfied val clause := by
  intro clause hclause
  simp only [muNegFiveCanonicalCrossDegreeClauses, List.mem_flatMap,
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
    obtain ⟨w, hw⟩ := hkernel sigma left ⟨z, hz8⟩ ⟨mask, hmask256⟩
      (muNegFiveZeroThreeFiberBit val left z)
      (hallowed left z hz8) (Bool.eq_false_iff.mpr hforbidden)
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

theorem muNegFiveZeroFourCrossDegreeClauses_satisfied
    (sigma : Bool) (val : DimacsValuation)
    (hallowed : ∀ left z, z < 8 →
      muNegFiveCanonicalFiberBitsAllowed 4 3 sigma left z
        (muNegFiveZeroThreeFiberBit val left z) = true) :
    ∀ clause ∈ muNegFiveCanonicalCrossDegreeClauses 4 3 sigma,
      dimacsClauseSatisfied val clause :=
  muNegFiveCanonicalCrossDegreeClauses_satisfied 4 3 sigma val
    muNegFiveZeroFour_forbiddenMask_has_satisfied_bit hallowed

theorem muNegFiveOneTwoCrossDegreeClauses_satisfied
    (sigma : Bool) (val : DimacsValuation)
    (hallowed : ∀ left z, z < 8 →
      muNegFiveCanonicalFiberBitsAllowed 6 4 sigma left z
        (muNegFiveZeroThreeFiberBit val left z) = true) :
    ∀ clause ∈ muNegFiveCanonicalCrossDegreeClauses 6 4 sigma,
      dimacsClauseSatisfied val clause :=
  muNegFiveCanonicalCrossDegreeClauses_satisfied 6 4 sigma val
    muNegFiveOneTwo_forbiddenMask_has_satisfied_bit hallowed

end Erdos85

#print axioms Erdos85.muNegFiveZeroFourCrossDegreeClauses_satisfied
#print axioms Erdos85.muNegFiveOneTwoCrossDegreeClauses_satisfied
