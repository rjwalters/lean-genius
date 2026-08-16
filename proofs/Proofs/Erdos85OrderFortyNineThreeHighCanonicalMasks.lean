import Proofs.Erdos85OrderFortyNineVariableHighCnfSemantics
import Proofs.Erdos85OrderFortyNineSmallHighCanonicalCapstone

/-!
# Canonical support masks for the two three-high cells
-/

namespace Erdos85

open Std Sat

def orderFortyNineThreeHighT0Masks : Array Nat :=
  #[0, 0, 0, 3, 5, 6,
    1, 1, 1, 1, 1, 1,
    2, 2, 2, 2, 2, 2,
    4, 4, 4, 4, 4, 4,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def orderFortyNineThreeHighT1Masks : Array Nat :=
  #[0, 0, 0, 7,
    1, 1, 1, 1, 1, 1, 1,
    2, 2, 2, 2, 2, 2, 2,
    4, 4, 4, 4, 4, 4, 4,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem orderFortyNineThreeHighT0Masks_size :
    orderFortyNineThreeHighT0Masks.size = 49 := by native_decide

theorem orderFortyNineThreeHighT1Masks_size :
    orderFortyNineThreeHighT1Masks.size = 49 := by native_decide

theorem orderFortyNineThreeHighT0Masks_high_zero :
    OrderFortyNineVariableHighMasksZero (3 : Fin 50)
      orderFortyNineThreeHighT0Masks := by
  intro a w
  fin_cases a <;> fin_cases w <;> native_decide

theorem orderFortyNineThreeHighT1Masks_high_zero :
    OrderFortyNineVariableHighMasksZero (3 : Fin 50)
      orderFortyNineThreeHighT1Masks := by
  intro a w
  fin_cases a <;> fin_cases w <;> native_decide

theorem orderFortyNineVariableHighPartitionExcluded_of_high_zero_three
    {masks : Array Nat}
    (hzero : OrderFortyNineVariableHighMasksZero (3 : Fin 50) masks) :
    OrderFortyNineVariableHighPartitionExcluded (3 : Fin 50) masks := by
  intro y a w htrue
  rw [hzero a w] at htrue
  contradiction

theorem orderFortyNineThreeHighT0Masks_partitionExcluded :
    OrderFortyNineVariableHighPartitionExcluded (3 : Fin 50)
      orderFortyNineThreeHighT0Masks :=
  orderFortyNineVariableHighPartitionExcluded_of_high_zero_three
    orderFortyNineThreeHighT0Masks_high_zero

theorem orderFortyNineThreeHighT1Masks_partitionExcluded :
    OrderFortyNineVariableHighPartitionExcluded (3 : Fin 50)
      orderFortyNineThreeHighT1Masks :=
  orderFortyNineVariableHighPartitionExcluded_of_high_zero_three
    orderFortyNineThreeHighT1Masks_high_zero

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem orderFortyNineDegreeBlocks_three_nonzero :
    ∀ clause ∈ (orderFortyNineDegreeBlocks 3).clauses,
      DimacsClauseNonzero clause := by
  have hcheck :
      (orderFortyNineDegreeBlocks 3).clauses.all fun clause =>
        clause.all fun lit => lit != 0 := by
    native_decide
  simp only [Array.all_eq_true] at hcheck
  intro clause hclause lit hlit
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hclause
  have hclauseCheck := hcheck i hi
  simp only [List.all_eq_true] at hclauseCheck
  have hlitCheck := hclauseCheck lit hlit
  simpa using hlitCheck

theorem orderFortyNineGeneratedVariableHighSatCnf_three_covered
    (masks : Array Nat) :
    OrderFortyNineVariableCnfCoveredBySegments (3 : Fin 50) masks
      (orderFortyNineGeneratedVariableHighSatCnf (3 : Fin 50) masks) := by
  constructor
  intro clause hclause
  simp only [orderFortyNineGeneratedVariableHighSatCnf, Array.mem_append,
    dimacsFormulaToSatClauses, Array.mem_map] at hclause
  rcases hclause with ((hfixed | hc4) | hdegree) | hpartition
  · obtain ⟨source, hsource, rfl⟩ := hfixed
    exact Or.inl ⟨source, hsource,
      orderFortyNineVariableFixedClauses_nonzero _ masks source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hc4
    exact Or.inr <| Or.inl ⟨source, hsource,
      orderFortyNineC4Clauses_nonzero source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hdegree
    exact Or.inr <| Or.inr <| Or.inl ⟨source, hsource,
      orderFortyNineDegreeBlocks_three_nonzero source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hpartition
    exact Or.inr <| Or.inr <| Or.inr ⟨source, hsource,
      orderFortyNineVariablePartitionClauses_nonzero _ masks source hsource,
      rfl⟩

theorem false_of_orderFortyNine_generated_h3_lrat
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3 masks edges)
    (hexcluded : OrderFortyNineVariableHighPartitionExcluded (3 : Fin 50) masks)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedVariableHighSatCnf (3 : Fin 50) masks)) : False := by
  obtain ⟨val, hsegments, _⟩ :=
    orderFortyNineVariableCnfSegments_satisfied (by omega) hc hexcluded
  have hsat := sat_of_orderFortyNineVariableCnfSegmentsSatisfied_of_covered
    hsegments (orderFortyNineGeneratedVariableHighSatCnf_three_covered masks)
  have hunsat := Std.Tactic.BVDecide.LRAT.check_sound proof _ hcheck
  have hfalse := hunsat (satAssignmentOfDimacs val)
  rw [hsat] at hfalse
  contradiction

theorem false_of_orderFortyNine_generated_h3_t0_lrat
    {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3
      orderFortyNineThreeHighT0Masks edges)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedVariableHighSatCnf (3 : Fin 50)
        orderFortyNineThreeHighT0Masks)) : False :=
  false_of_orderFortyNine_generated_h3_lrat hc
    orderFortyNineThreeHighT0Masks_partitionExcluded proof hcheck

theorem false_of_orderFortyNine_generated_h3_t1_lrat
    {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3
      orderFortyNineThreeHighT1Masks edges)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedVariableHighSatCnf (3 : Fin 50)
        orderFortyNineThreeHighT1Masks)) : False :=
  false_of_orderFortyNine_generated_h3_lrat hc
    orderFortyNineThreeHighT1Masks_partitionExcluded proof hcheck

theorem orderFortyNineThreeHighRepresentativeMasks_zero_eq :
    OrderFortyNineSmallHighCensus.threeHighRepresentativeMasks 0 =
      orderFortyNineThreeHighT0Masks := by
  native_decide

theorem orderFortyNineThreeHighRepresentativeMasks_one_eq :
    OrderFortyNineSmallHighCensus.threeHighRepresentativeMasks 1 =
      orderFortyNineThreeHighT1Masks := by
  native_decide

theorem threeHighCanonicalRepresentativeExcluded_zero_of_lrat
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedVariableHighSatCnf (3 : Fin 50)
        (OrderFortyNineSmallHighCensus.threeHighRepresentativeMasks 0))) :
    ThreeHighCanonicalRepresentativeExcluded 0 := by
  intro edges hc
  rw [orderFortyNineThreeHighRepresentativeMasks_zero_eq] at hc hcheck
  exact false_of_orderFortyNine_generated_h3_t0_lrat hc proof hcheck

theorem threeHighCanonicalRepresentativeExcluded_one_of_lrat
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedVariableHighSatCnf (3 : Fin 50)
        (OrderFortyNineSmallHighCensus.threeHighRepresentativeMasks 1))) :
    ThreeHighCanonicalRepresentativeExcluded 1 := by
  intro edges hc
  rw [orderFortyNineThreeHighRepresentativeMasks_one_eq] at hc hcheck
  exact false_of_orderFortyNine_generated_h3_t1_lrat hc proof hcheck

end Erdos85
