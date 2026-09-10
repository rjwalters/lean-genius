import U20Inputs
namespace U20Hall
open Erdos85 U20CoverageLiterals
open scoped BigOperators
attribute [local irreducible] threeHighCrossDomain

theorem double_count (cross : ThreeHighCross) (S : Finset (Fin 15)) :
    (∑ i ∈ S, encodedRowDegree (cross i)) =
      ∑ j : Fin 8, (S.filter fun i => cross i j).card := by
  simp only [encodedRowDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

def S : Finset (Fin 15) := {0,1,2,5,6,7,9,10,11,12,14}
def caps : Fin 8 → Nat := ![0,2,2,2,1,1,1,1]
theorem caps_checked (j : Fin 8) :
    (domains j).all (fun T => decide ((S ∩ T).card ≤ caps j)) = true := by
  fin_cases j <;> decide

theorem impossible (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true) : False := by
  have hd := U20CoverageInputs.domains_complete cross hc he
  have hb : ∀ j : Fin 8, (S.filter fun i => cross i j).card ≤ caps j := by
    intro j
    have h := of_decide_eq_true ((List.all_eq_true.mp (caps_checked j)) _ (hd j))
    have hset : S.filter (fun i => cross i j) = S ∩ threeHighCrossColumns cross j := by
      ext i
      simp [threeHighCrossColumns]
    rw [hset]
    exact h
  have hm : ∀ i, encodedRowDegree (cross i) = 4 - encodedRowDegree (U i) := by
    intro i
    have h := (threeHighCrossDomain_margins U R cross hc).1 i
    omega
  have hsum : (∑ i ∈ S, encodedRowDegree (cross i)) = 11 := by
    simp_rw [hm]
    decide
  have hle := Finset.sum_le_sum (fun (j : Fin 8) (_ : j ∈ Finset.univ) => hb j)
  rw [← double_count cross S, hsum] at hle
  have hcaps : (∑ j : Fin 8, caps j) = 10 := by decide
  rw [hcaps] at hle
  omega

theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 16)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)))
    (he : encodedExternalBlockCap (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 16)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 9 9 16)))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 14)) cross) := by
  rw [← U_eq, ← R_eq] at hc he ⊢
  exact (impossible cross hc he).elim
end U20Hall
#print axioms U20Hall.double_count
#print axioms U20Hall.caps_checked
#print axioms U20Hall.impossible

#print axioms U20Hall.no_joint
