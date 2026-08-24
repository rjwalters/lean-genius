import Proofs.Erdos85FinalDyadicDefectCutDegreeCensus

/-!
# Four-level adjacency profile of the final exceptional vector

The two defect-cut classes are exactly the level sets of the adjacency image
of the canonical exceptional occupancy sign.  This is the pointwise bridge
from the global cut census to a quadratic energy calculation.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def finalDyadicExceptionalAdjacencyBalance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (q : ℕ) (v : V) : ℤ :=
  ∑ w ∈ G.neighborFinset v, exceptionalOccupancySign G S q w

/-- On `S`, the exceptional adjacency balance is one on the low class and
two on the high class. -/
theorem finalDyadic_positiveShore_exceptionalAdjacencyBalance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (v : V) (hv : v ∈ S) :
    finalDyadicExceptionalAdjacencyBalance G S q v =
      if v ∈ finalDyadicPositiveHighCutCenters G S q r then 2 else 1 := by
  let D := secondOrderDefectGraph G
  let N := D.neighborFinset v
  let a := (N \ S).card
  let t := finalDyadicExceptionalAdjacencyBalance G S q v
  let P := finalDyadicPositiveHighCutCenters G S q r
  have hDcard : N.card = q - 1 := by
    rw [D.card_neighborFinset_eq_degree,
      binarySquare_regular_secondOrderDefect_degree_eq
        G hfree hq hreg hcard]
  have hpartition := Finset.card_inter_add_card_sdiff N S
  have hsigned := sum_cutSign_over_finset N S
  have hcomp := finalDyadic_companionDefect_apply_of_displacement
    G hfree hqa hreg hcard S hdiv hdisp v
  simp only [if_pos hv, mul_one] at hcomp
  have heq : (q : ℤ) * t = 2 * (a + r : ℕ) := by
    change (N ∩ S).card + a = N.card at hpartition
    rw [hDcard] at hpartition
    have hqsubZ : ((q - 1 : ℕ) : ℤ) = q - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hpartZ := congrArg (fun n : ℕ => (n : ℤ)) hpartition
    push_cast at hpartZ
    rw [hqsubZ] at hpartZ
    rw [hsigned, hDcard, hqsubZ] at hcomp
    change 2 * ((N ∩ S).card : ℤ) - (q - 1) =
      (q - 1) + 2 * r - q * t at hcomp
    push_cast
    nlinarith
  have htwo := finalDyadic_positiveShore_defectCutDegree_twoLevel
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf v hv
  by_cases hvP : v ∈ P
  · have ha : a = q - r := (Finset.mem_filter.mp hvP).2
    rw [if_pos hvP]
    change t = 2
    rw [ha] at heq
    have hrq : r ≤ q := by rw [hqa]; omega
    push_cast [Nat.cast_sub hrq] at heq
    nlinarith
  · have hnotHigh : a ≠ q - r := by
      intro ha
      exact hvP (Finset.mem_filter.mpr ⟨hv, ha⟩)
    have ha : a = 2 ^ j - r := htwo.resolve_right hnotHigh
    rw [if_neg hvP]
    change t = 1
    rw [ha, hqa] at heq
    have hrh : r ≤ 2 ^ j := by omega
    push_cast [Nat.cast_sub hrh] at heq
    nlinarith

/-- Off `S`, the exceptional adjacency balance is zero on the low class and
minus one on the high class. -/
theorem finalDyadic_negativeShore_exceptionalAdjacencyBalance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (v : V) (hv : v ∉ S) :
    finalDyadicExceptionalAdjacencyBalance G S q v =
      if v ∈ finalDyadicNegativeHighCutCenters G S j r then -1 else 0 := by
  let D := secondOrderDefectGraph G
  let N := D.neighborFinset v
  let a := (N ∩ S).card
  let t := finalDyadicExceptionalAdjacencyBalance G S q v
  let M := finalDyadicNegativeHighCutCenters G S j r
  have hDcard : N.card = q - 1 := by
    rw [D.card_neighborFinset_eq_degree,
      binarySquare_regular_secondOrderDefect_degree_eq
        G hfree hq hreg hcard]
  have hsigned := sum_cutSign_over_finset N S
  have hcomp := finalDyadic_companionDefect_apply_of_displacement
    G hfree hqa hreg hcard S hdiv hdisp v
  simp only [if_neg hv, mul_neg, mul_one] at hcomp
  have heq : 2 * (a : ℤ) = 2 * r - q * t := by
    have hqsubZ : ((q - 1 : ℕ) : ℤ) = q - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hsigned, hDcard, hqsubZ] at hcomp
    change 2 * (a : ℤ) - (q - 1) =
      -(q - 1) + 2 * r - q * t at hcomp
    nlinarith
  have htwo := finalDyadic_negativeShore_defectCutDegree_twoLevel
    G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf v hv
  by_cases hvM : v ∈ M
  · have ha : a = 2 ^ j + r := (Finset.mem_filter.mp hvM).2
    rw [if_pos hvM]
    change t = -1
    rw [ha, hqa] at heq
    push_cast at heq
    nlinarith
  · have hvSc : v ∈ (Sᶜ : Finset V) := Finset.mem_compl.mpr hv
    have hnotHigh : a ≠ 2 ^ j + r := by
      intro ha
      exact hvM (Finset.mem_filter.mpr ⟨hvSc, ha⟩)
    have ha : a = r := htwo.resolve_right hnotHigh
    rw [if_neg hvM]
    change t = 0
    rw [ha] at heq
    nlinarith

end

end Erdos85

#print axioms Erdos85.finalDyadic_positiveShore_exceptionalAdjacencyBalance
#print axioms Erdos85.finalDyadic_negativeShore_exceptionalAdjacencyBalance
