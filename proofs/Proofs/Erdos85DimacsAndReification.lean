import Proofs.Erdos85SequentialCounterReification

/-! # A fresh DIMACS variable reifying a conjunction -/

namespace Erdos85

/-- The three standard Tseitin clauses saying that `top + 1` is equivalent
to the conjunction of two pre-existing signed literals. -/
def dimacsAndClauses (top : Nat) (left right : Int) : Array DimacsClause :=
  #[[-((top + 1 : Nat) : Int), left],
    [-((top + 1 : Nat) : Int), right],
    [((top + 1 : Nat) : Int), -left, -right]]

/-- Extend a valuation at the fresh identifier `top + 1` by the conjunction
of the truth values of `left` and `right`. -/
def dimacsAndVal (inputVal : DimacsValuation) (top : Nat)
    (left right : Int) : DimacsValuation := fun id =>
  if id = top + 1 then
    dimacsLitValue inputVal left && dimacsLitValue inputVal right
  else inputVal id

theorem dimacsAndVal_input (inputVal : DimacsValuation) (top : Nat)
    (left right : Int) {id : Nat} (hid : id ≤ top) :
    dimacsAndVal inputVal top left right id = inputVal id := by
  simp [dimacsAndVal]
  omega

/-- The canonical conjunction extension satisfies its three Tseitin
clauses.  The bounds ensure neither input literal aliases the fresh output. -/
theorem dimacsAndClauses_formulaSatisfied
    (inputVal : DimacsValuation) (top : Nat) (left right : Int)
    (hleft0 : left ≠ 0) (hright0 : right ≠ 0)
    (hleft : left.natAbs ≤ top) (hright : right.natAbs ≤ top) :
    dimacsFormulaSatisfied (dimacsAndVal inputVal top left right)
      (dimacsAndClauses top left right) := by
  intro clause hclause
  simp [dimacsAndClauses] at hclause
  have hfresh : ¬top + 1 ≤ top := by omega
  have hleftVal :
      dimacsLitValue (dimacsAndVal inputVal top left right) left =
        dimacsLitValue inputVal left := by
    apply dimacsLitValue_eq_of_agree
    exact dimacsAndVal_input inputVal top left right hleft
  have hrightVal :
      dimacsLitValue (dimacsAndVal inputVal top left right) right =
        dimacsLitValue inputVal right := by
    apply dimacsLitValue_eq_of_agree
    exact dimacsAndVal_input inputVal top left right hright
  have hpositive : 0 < ((top + 1 : Nat) : Int) := by omega
  have habs : (((top : Int) + 1).natAbs) = top + 1 := by
    have hcast : (top : Int) + 1 = ((top + 1 : Nat) : Int) := by omega
    rw [hcast, Int.natAbs_natCast]
  have hfreshVal :
      dimacsLitValue (dimacsAndVal inputVal top left right)
          ((top + 1 : Nat) : Int) =
        (dimacsLitValue inputVal left && dimacsLitValue inputVal right) := by
    simp [dimacsLitValue, dimacsAndVal, habs]
  have hfreshNeg :
      dimacsLitValue (dimacsAndVal inputVal top left right)
          (-((top + 1 : Nat) : Int)) =
        !(dimacsLitValue inputVal left && dimacsLitValue inputVal right) := by
    rw [dimacsLitValue_neg _ (by omega)]
    rw [hfreshVal]
  rcases hclause with rfl | rfl | rfl
  · by_cases hl : dimacsLitValue inputVal left = true
    · refine ⟨left, by simp, ?_⟩
      simpa [hleftVal] using hl
    · refine ⟨-((top + 1 : Nat) : Int), by simp, ?_⟩
      rw [hfreshNeg]
      simp [Bool.eq_false_of_not_eq_true hl]
  · by_cases hr : dimacsLitValue inputVal right = true
    · refine ⟨right, by simp, ?_⟩
      simpa [hrightVal] using hr
    · refine ⟨-((top + 1 : Nat) : Int), by simp, ?_⟩
      rw [hfreshNeg]
      simp [Bool.eq_false_of_not_eq_true hr]
  · by_cases hl : dimacsLitValue inputVal left = true
    · by_cases hr : dimacsLitValue inputVal right = true
      · refine ⟨((top + 1 : Nat) : Int), by simp, ?_⟩
        rw [hfreshVal]
        simp [hl, hr]
      · refine ⟨-right, by simp, ?_⟩
        rw [dimacsLitValue_neg _ hright0, hrightVal]
        simp [Bool.eq_false_of_not_eq_true hr]
    · refine ⟨-left, by simp, ?_⟩
      rw [dimacsLitValue_neg _ hleft0, hleftVal]
      simp [Bool.eq_false_of_not_eq_true hl]

end Erdos85

#print axioms Erdos85.dimacsAndClauses_formulaSatisfied
