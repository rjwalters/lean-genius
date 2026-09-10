import Proofs.Erdos85MatchingNestedNormalForm
import Mathlib.Logic.Equiv.Fin.Basic

/-! Consecutive numeric coordinates for the three nonempty matchings on six vertices. -/
namespace Erdos85

def matchingFinSixAdj (m : ℕ) (i j : Fin 6) : Prop :=
  i ≠ j ∧ i.val / 2 = j.val / 2 ∧ i.val < 2 * m

instance matchingFinSixAdj_decidable (m : ℕ) : DecidableRel (matchingFinSixAdj m) :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ i.val / 2 = j.val / 2 ∧ i.val < 2 * m))

instance matchingNestedAdj_decidable (m k : ℕ) : DecidableRel (matchingNestedAdj m k) := by
  induction m with
  | zero => intro x y; exact isFalse id
  | succ m ih =>
    intro x y
    rcases x with i | x <;> rcases y with j | y
    · exact inferInstanceAs (Decidable (i ≠ j))
    · exact isFalse id
    · exact isFalse id
    · exact ih x y

private def oneEdgeSixCoordinates : matchingNestedVertices 1 4 ≃ Fin 6 := finSumFinEquiv

private def twoEdgeSixCoordinates : matchingNestedVertices 2 2 ≃ Fin 6 :=
  (Equiv.sumCongr (Equiv.refl (Fin 2)) finSumFinEquiv).trans finSumFinEquiv

private def threeEdgeSixCoordinates : matchingNestedVertices 3 0 ≃ Fin 6 :=
  (Equiv.sumCongr (Equiv.refl (Fin 2))
    ((Equiv.sumCongr (Equiv.refl (Fin 2)) finSumFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv

private theorem oneEdgeSixCoordinates_adj (i j : Fin 6) :
    matchingNestedAdj 1 4 (oneEdgeSixCoordinates.symm i) (oneEdgeSixCoordinates.symm j) ↔
      matchingFinSixAdj 1 i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem twoEdgeSixCoordinates_adj (i j : Fin 6) :
    matchingNestedAdj 2 2 (twoEdgeSixCoordinates.symm i) (twoEdgeSixCoordinates.symm j) ↔
      matchingFinSixAdj 2 i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem threeEdgeSixCoordinates_adj (i j : Fin 6) :
    matchingNestedAdj 3 0 (threeEdgeSixCoordinates.symm i) (threeEdgeSixCoordinates.symm j) ↔
      matchingFinSixAdj 3 i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem matching_nested_six_coordinates {m k : ℕ}
    (hcases : (m = 1 ∧ k = 4) ∨ (m = 2 ∧ k = 2) ∨ (m = 3 ∧ k = 0)) :
    ∃ e : matchingNestedVertices m k ≃ Fin 6,
      ∀ i j, matchingNestedAdj m k (e.symm i) (e.symm j) ↔ matchingFinSixAdj m i j := by
  rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨oneEdgeSixCoordinates, oneEdgeSixCoordinates_adj⟩
  · exact ⟨twoEdgeSixCoordinates, twoEdgeSixCoordinates_adj⟩
  · exact ⟨threeEdgeSixCoordinates, threeEdgeSixCoordinates_adj⟩

end Erdos85
#print axioms Erdos85.matching_nested_six_coordinates
