import Proofs.Erdos85OrderFortyNineVariableHighCnfSemantics

/-!
# Canonical support masks for the three five-high cells

These arrays are decoded from the 230-unit fixed prefixes of the recovered
`h5_t0`, `h5_t1`, and `h5_t2` DIMACS instances.  Vertices `0..4` are the five
high vertices and have zero support masks; vertices `5..48` are ordered first
by triple supports, then pair supports, singleton supports, and empty support.
-/

namespace Erdos85

def orderFortyNineFiveHighT0Masks : Array Nat :=
  #[0, 0, 0, 0, 0,
    3, 5, 9, 17, 6, 10, 18, 12, 20, 24,
    1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 4, 4,
    8, 8, 8, 8, 16, 16, 16, 16,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def orderFortyNineFiveHighT1Masks : Array Nat :=
  #[0, 0, 0, 0, 0,
    7, 9, 17, 10, 18, 12, 20, 24,
    1, 1, 1, 1, 1, 2, 2, 2, 2, 2,
    4, 4, 4, 4, 4, 8, 8, 8, 8, 16, 16, 16, 16,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def orderFortyNineFiveHighT2Masks : Array Nat :=
  #[0, 0, 0, 0, 0,
    7, 25, 10, 18, 12, 20,
    1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2,
    4, 4, 4, 4, 4, 8, 8, 8, 8, 8,
    16, 16, 16, 16, 16,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem orderFortyNineFiveHighT0Masks_size :
    orderFortyNineFiveHighT0Masks.size = 49 := by native_decide

theorem orderFortyNineFiveHighT1Masks_size :
    orderFortyNineFiveHighT1Masks.size = 49 := by native_decide

theorem orderFortyNineFiveHighT2Masks_size :
    orderFortyNineFiveHighT2Masks.size = 49 := by native_decide

theorem orderFortyNineFiveHighT0Masks_high_zero :
    OrderFortyNineVariableHighMasksZero (5 : Fin 50)
      orderFortyNineFiveHighT0Masks := by
  intro a w
  fin_cases a <;> fin_cases w <;> native_decide

theorem orderFortyNineFiveHighT1Masks_high_zero :
    OrderFortyNineVariableHighMasksZero (5 : Fin 50)
      orderFortyNineFiveHighT1Masks := by
  intro a w
  fin_cases a <;> fin_cases w <;> native_decide

theorem orderFortyNineFiveHighT2Masks_high_zero :
    OrderFortyNineVariableHighMasksZero (5 : Fin 50)
      orderFortyNineFiveHighT2Masks := by
  intro a w
  fin_cases a <;> fin_cases w <;> native_decide

theorem orderFortyNineVariableHighPartitionExcluded_of_high_zero
    {h : OrderFortyNineHighCount} {masks : Array Nat}
    (hzero : OrderFortyNineVariableHighMasksZero h masks) :
    OrderFortyNineVariableHighPartitionExcluded h masks := by
  intro y a w htrue
  rw [hzero a w] at htrue
  contradiction

theorem orderFortyNineFiveHighT0Masks_partitionExcluded :
    OrderFortyNineVariableHighPartitionExcluded (5 : Fin 50)
      orderFortyNineFiveHighT0Masks :=
  orderFortyNineVariableHighPartitionExcluded_of_high_zero
    orderFortyNineFiveHighT0Masks_high_zero

theorem orderFortyNineFiveHighT1Masks_partitionExcluded :
    OrderFortyNineVariableHighPartitionExcluded (5 : Fin 50)
      orderFortyNineFiveHighT1Masks :=
  orderFortyNineVariableHighPartitionExcluded_of_high_zero
    orderFortyNineFiveHighT1Masks_high_zero

theorem orderFortyNineFiveHighT2Masks_partitionExcluded :
    OrderFortyNineVariableHighPartitionExcluded (5 : Fin 50)
      orderFortyNineFiveHighT2Masks :=
  orderFortyNineVariableHighPartitionExcluded_of_high_zero
    orderFortyNineFiveHighT2Masks_high_zero

theorem false_of_orderFortyNine_generated_h5_t0_lrat
    {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 5
      orderFortyNineFiveHighT0Masks edges)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50)
        orderFortyNineFiveHighT0Masks)) : False :=
  false_of_orderFortyNine_generated_h5_lrat hc
    orderFortyNineFiveHighT0Masks_partitionExcluded proof hcheck

theorem false_of_orderFortyNine_generated_h5_t1_lrat
    {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 5
      orderFortyNineFiveHighT1Masks edges)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50)
        orderFortyNineFiveHighT1Masks)) : False :=
  false_of_orderFortyNine_generated_h5_lrat hc
    orderFortyNineFiveHighT1Masks_partitionExcluded proof hcheck

theorem false_of_orderFortyNine_generated_h5_t2_lrat
    {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 5
      orderFortyNineFiveHighT2Masks edges)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50)
        orderFortyNineFiveHighT2Masks)) : False :=
  false_of_orderFortyNine_generated_h5_lrat hc
    orderFortyNineFiveHighT2Masks_partitionExcluded proof hcheck

end Erdos85
