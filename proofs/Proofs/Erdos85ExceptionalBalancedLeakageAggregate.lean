import Proofs.Erdos85ExceptionalBalancedLeakageCapacity
import Proofs.Erdos85ExceptionalLeakageBoundarySupport

/-!
# Aggregate balanced capacity of exceptional leakage

Summing the balanced-center packing inequality over precisely the outside
vertices touched by empty-pole leakage and substituting the exact leakage
mass produces a global constraint.  The boundary's component embedding then
turns this into a fraction-free lower bound on the containing defect
component.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Final-dyadic aggregate of the balanced local packing inequalities over
the leakage boundary. -/
theorem binarySquare_finalDyadic_exceptionalEmpty_balancedLeakage_aggregate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    2 * q * ((emptyLineCenters G S).card *
          (q - (fullLineCenters G S q ∪ emptyLineCenters G S).card)) +
        (2 * S.card + q) *
          (exceptionalEmptyLeakageBoundary G S q).card ≤
      2 * q * q * (exceptionalEmptyLeakageBoundary G S q).card := by
  let C := fullLineCenters G S q ∪ emptyLineCenters G S
  let E := emptyLineCenters G S
  let D := secondOrderDefectGraph G
  let T := exceptionalEmptyLeakageBoundary G S q
  let load : V → ℕ := fun x => (D.neighborFinset x ∩ E).card
  have hlocal : ∀ x ∈ T,
      2 * q * load x + 2 * S.card + q ≤ 2 * q * q := by
    intro x hxT
    have hxCcompl : x ∈ Cᶜ := (Finset.mem_filter.mp hxT).1
    have hxNotExceptional : x ∉ exceptionalSignedSupport G S q := by
      rw [exceptionalSignedSupport_eq_full_union_empty]
      exact Finset.mem_compl.mp hxCcompl
    exact binarySquare_finalDyadic_outsideExceptional_emptyLeakage_capacity
      G hfree hqa hreg hcard S hdiv hemptyClique x hxNotExceptional
  have hlocalSum := Finset.sum_le_sum fun x hx => hlocal x hx
  have hsumAll := binarySquare_emptyPoles_outsideExceptional_defectIncidence_sum
    G hfree hq hreg hcard S hemptyClique
  change (∑ x ∈ Cᶜ, load x) = E.card * (q - C.card) at hsumAll
  have hTsub : T ⊆ Cᶜ := fun x hx => (Finset.mem_filter.mp hx).1
  have hsumT : (∑ x ∈ T, load x) = E.card * (q - C.card) := by
    rw [← hsumAll]
    apply Finset.sum_subset hTsub
    intro x hxC hxT
    have hxNotPos : ¬ 0 < load x := by
      intro hxPos
      exact hxT (Finset.mem_filter.mpr ⟨hxC, hxPos⟩)
    omega
  change
    (∑ x ∈ T, (2 * q * load x + 2 * S.card + q)) ≤
      ∑ _x ∈ T, 2 * q * q at hlocalSum
  have hloadScale : (∑ x ∈ T, 2 * q * load x) =
      2 * q * ∑ x ∈ T, load x := by
    rw [Finset.mul_sum]
  change 2 * q * (E.card * (q - C.card)) +
      (2 * S.card + q) * T.card ≤ 2 * q * q * T.card
  calc
    2 * q * (E.card * (q - C.card)) +
          (2 * S.card + q) * T.card =
        ∑ x ∈ T, (2 * q * load x + 2 * S.card + q) := by
          rw [← hsumT]
          simp only [Finset.sum_add_distrib, Finset.sum_const,
            nsmul_eq_mul]
          rw [hloadScale]
          simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          ring
    _ ≤ ∑ _x ∈ T, 2 * q * q := hlocalSum
    _ = 2 * q * q * T.card := by simp [Nat.mul_comm]

/-- Population-only form, eliminating the shore size with the exact final
full-minus-empty mass identity. -/
theorem binarySquare_finalDyadic_exceptionalEmpty_balancedLeakage_intrinsic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v) :
    2 * q * ((emptyLineCenters G S).card *
          (q - (fullLineCenters G S q ∪ emptyLineCenters G S).card)) +
        (q * q + (fullLineCenters G S q).card + q) *
          (exceptionalEmptyLeakageBoundary G S q).card ≤
      (2 * q * q + (emptyLineCenters G S).card) *
        (exceptionalEmptyLeakageBoundary G S q).card := by
  let E := emptyLineCenters G S
  let F := fullLineCenters G S q
  let C := F ∪ E
  let T := exceptionalEmptyLeakageBoundary G S q
  have hagg :=
    binarySquare_finalDyadic_exceptionalEmpty_balancedLeakage_aggregate
      G hfree hq hqa hreg hcard S hdiv hemptyClique
  change 2 * q * (E.card * (q - C.card)) +
      (2 * S.card + q) * T.card ≤ 2 * q * q * T.card at hagg
  have hmassZ := finalDyadic_full_sub_empty_eq_cutDisplacement
    G hqa hreg S hdiv
  rw [hcard] at hmassZ
  change (F.card : ℤ) - E.card =
    2 * (S.card : ℤ) - (q * q : ℕ) at hmassZ
  push_cast at hmassZ
  have hmass : 2 * S.card + E.card = q * q + F.card := by
    omega
  have hadd := Nat.add_le_add_right hagg (E.card * T.card)
  change 2 * q * (E.card * (q - C.card)) +
      (q * q + F.card + q) * T.card ≤
    (2 * q * q + E.card) * T.card
  calc
    2 * q * (E.card * (q - C.card)) +
          (q * q + F.card + q) * T.card =
        (2 * q * (E.card * (q - C.card)) +
          (2 * S.card + q) * T.card) + E.card * T.card := by
            rw [← hmass]
            ring
    _ ≤ 2 * q * q * T.card + E.card * T.card := hadd
    _ = (2 * q * q + E.card) * T.card := by ring

/-- Component-order form: the containing component must accommodate the
exceptional core, while its leakage boundary still pays the balanced local
capacity charge. -/
theorem binarySquare_finalDyadic_exceptionalEmpty_balancedLeakage_component_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    (pole : V) (hpole : pole ∈ emptyLineCenters G S) :
    2 * q * ((emptyLineCenters G S).card *
          (q - (fullLineCenters G S q ∪ emptyLineCenters G S).card)) +
        (2 * S.card + q) *
          (exceptionalEmptyLeakageBoundary G S q).card +
        2 * q * q *
          (fullLineCenters G S q ∪ emptyLineCenters G S).card ≤
      2 * q * q *
        ((secondOrderDefectGraph G).connectedComponentMk pole).supp.ncard := by
  let C := fullLineCenters G S q ∪ emptyLineCenters G S
  let T := exceptionalEmptyLeakageBoundary G S q
  let m := ((secondOrderDefectGraph G).connectedComponentMk pole).supp.ncard
  have hagg :=
    binarySquare_finalDyadic_exceptionalEmpty_balancedLeakage_aggregate
      G hfree hq hqa hreg hcard S hdiv hemptyClique
  change 2 * q * ((emptyLineCenters G S).card * (q - C.card)) +
      (2 * S.card + q) * T.card ≤ 2 * q * q * T.card at hagg
  have hcomponent := exceptional_card_add_leakageBoundary_card_le_component
    G hfree (by omega) hreg S hemptyClique pole hpole
  change C.card + T.card ≤ m at hcomponent
  have hmul := Nat.mul_le_mul_left (2 * q * q) hcomponent
  rw [Nat.mul_add] at hmul
  change 2 * q * ((emptyLineCenters G S).card * (q - C.card)) +
      (2 * S.card + q) * T.card + 2 * q * q * C.card ≤
    2 * q * q * m
  omega

end

end Erdos85

#print axioms
  Erdos85.binarySquare_finalDyadic_exceptionalEmpty_balancedLeakage_aggregate
#print axioms
  Erdos85.binarySquare_finalDyadic_exceptionalEmpty_balancedLeakage_intrinsic
#print axioms
  Erdos85.binarySquare_finalDyadic_exceptionalEmpty_balancedLeakage_component_order
