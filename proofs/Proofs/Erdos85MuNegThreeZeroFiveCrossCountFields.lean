import Proofs.Erdos85MuNegThreeZeroFiveFiniteSemantics
import Proofs.Erdos85MuNegOneOneFourCrossCountFields

/-! # Cross defect count fields for h305 -/

namespace Erdos85

open Finset

def MuNegThreeZeroFiveCrossExteriorSplit
    {X : Type*} (R : SimpleGraph X) [DecidableRel R.Adj]
    (u v : ZMod 8 → X) (su sv : ZMod 8 → ℤ) : Prop :=
  (∀ i,
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      R.Adj (u i) (v j) ∧ sv j = su i).card = 2 ∧
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      R.Adj (u i) (v j) ∧ sv j ≠ su i).card = 1) ∧
  (∀ j,
    ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
      R.Adj (u i) (v j) ∧ su i = sv j).card = 2 ∧
    ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
      R.Adj (u i) (v j) ∧ su i ≠ sv j).card = 1)

private theorem countP_add_countP_not_h305
    {A : Type*} (l : List A) (p : A → Bool) :
    l.countP p + l.countP (fun x ↦ !p x) = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => cases hp : p a <;> simp [hp] <;> omega

private theorem countP_not_eq_three_of_class_four_of_pos_one
    {A : Type*} (l : List A) (cls edge : A → Bool)
    (hclass : (l.filter cls).length = 4)
    (hpos : (l.filter cls).countP edge = 1) :
    (l.filter cls).countP (fun x ↦ !edge x) = 3 := by
  have hsum := countP_add_countP_not_h305 (l.filter cls) edge
  omega


private theorem h305Sign_row_same_length_four
    (σ : Bool) (i : Nat) (hi : i < 8) :
    ((List.range 8).filter fun j ↦
      muNegOneSign σ i == muNegOneSign σ (8 + j)).length = 4 := by
  cases σ <;> interval_cases i <;> decide

private theorem h305Sign_row_opp_length_four
    (σ : Bool) (i : Nat) (hi : i < 8) :
    ((List.range 8).filter fun j ↦
      !(muNegOneSign σ i == muNegOneSign σ (8 + j))).length = 4 := by
  cases σ <;> interval_cases i <;> decide

private theorem h305Sign_col_same_length_four
    (σ : Bool) (j : Nat) (hj : j < 8) :
    ((List.range 8).filter fun i ↦
      muNegOneSign σ i == muNegOneSign σ (8 + j)).length = 4 := by
  cases σ <;> interval_cases j <;> decide

private theorem h305Sign_col_opp_length_four
    (σ : Bool) (j : Nat) (hj : j < 8) :
    ((List.range 8).filter fun i ↦
      !(muNegOneSign σ i == muNegOneSign σ (8 + j))).length = 4 := by
  cases σ <;> interval_cases j <;> decide

/-- The four cross-defect count fields required by the finite semantics.
`D` is the complement of the exterior-pair graph on the ordered cross block. -/
theorem muNegThreeZeroFive_crossDefect_count_fields
    {X : Type*} (R : SimpleGraph X) [DecidableRel R.Adj]
    (u v : ZMod 8 → X) (su sv : ZMod 8 → ℤ)
    (hsu : ∀ i, su i = -1 ∨ su i = 1)
    (hsv : ∀ j, sv j = -1 ∨ sv j = 1)
    (hphase : MuNegOneOneFourAlternatingSignPhases su sv)
    (hcross : MuNegThreeZeroFiveCrossExteriorSplit R u v su sv) :
    let σ := muNegOneSigmaOf su sv
    let D : Nat → Nat → Bool := fun i j ↦
      !(decide (R.Adj (u (i : ZMod 8)) (v (j : ZMod 8))))
    (∀ i, i < 8 →
      (((List.range 8).filter fun j ↦
        muNegOneSign σ i == muNegOneSign σ (8 + j)).countP fun j ↦ D i j) = 2) ∧
    (∀ i, i < 8 →
      (((List.range 8).filter fun j ↦
        !(muNegOneSign σ i == muNegOneSign σ (8 + j))).countP fun j ↦ D i j) = 3) ∧
    (∀ j, j < 8 →
      (((List.range 8).filter fun i ↦
        muNegOneSign σ i == muNegOneSign σ (8 + j)).countP fun i ↦ D i j) = 2) ∧
    (∀ j, j < 8 →
      (((List.range 8).filter fun i ↦
        !(muNegOneSign σ i == muNegOneSign σ (8 + j))).countP fun i ↦ D i j) = 3) := by
  dsimp only
  let σ := muNegOneSigmaOf su sv
  let E : Nat → Nat → Bool := fun i j ↦
    decide (R.Adj (u (i : ZMod 8)) (v (j : ZMod 8)))
  have hsame (i j : Nat) (hi : i < 8) (hj : j < 8) :
      (muNegOneSign σ i == muNegOneSign σ (8 + j)) =
        decide (su (i : ZMod 8) = sv (j : ZMod 8)) := by
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    exact (muNegOneSigma_coherence su sv hsu hsv hphase i j hi hj).symm
  have hopp (i j : Nat) (hi : i < 8) (hj : j < 8) :
      ((!(muNegOneSign σ i == muNegOneSign σ (8 + j))) : Bool) =
        decide (su (i : ZMod 8) ≠ sv (j : ZMod 8)) := by
    rw [hsame i j hi hj]
    simp
  have hrowSameEdge (i : Nat) (hi : i < 8) :
      (((List.range 8).filter fun j ↦
        muNegOneSign σ i == muNegOneSign σ (8 + j)).countP fun j ↦ E i j) = 2 := by
    have hf : ((List.range 8).filter fun j ↦
        muNegOneSign σ i == muNegOneSign σ (8 + j)) =
        ((List.range 8).filter fun (j : Nat) ↦
          decide (su (i : ZMod 8) = sv (j : ZMod 8))) := by
      apply List.filter_congr
      intro j hj
      exact hsame i j hi (List.mem_range.mp hj)
    rw [hf]
    dsimp only [E]
    rw [zmodEight_range_filter_countP_eq_univ_filter_card
      (fun z ↦ decide (su (i : ZMod 8) = sv z))
      (fun z ↦ decide (R.Adj (u (i : ZMod 8)) (v z)))]
    simpa [E, eq_comm, and_comm] using (hcross.1 (i : ZMod 8)).1
  have hrowOppEdge (i : Nat) (hi : i < 8) :
      (((List.range 8).filter fun j ↦
        !(muNegOneSign σ i == muNegOneSign σ (8 + j))).countP fun j ↦ E i j) = 1 := by
    have hf : ((List.range 8).filter fun j ↦
        !(muNegOneSign σ i == muNegOneSign σ (8 + j))) =
        ((List.range 8).filter fun (j : Nat) ↦
          decide (su (i : ZMod 8) ≠ sv (j : ZMod 8))) := by
      apply List.filter_congr
      intro j hj
      exact hopp i j hi (List.mem_range.mp hj)
    rw [hf]
    dsimp only [E]
    rw [zmodEight_range_filter_countP_eq_univ_filter_card
      (fun z ↦ decide (su (i : ZMod 8) ≠ sv z))
      (fun z ↦ decide (R.Adj (u (i : ZMod 8)) (v z)))]
    simpa [E, ne_eq, and_comm, ne_comm] using (hcross.1 (i : ZMod 8)).2
  have hcolSameEdge (j : Nat) (hj : j < 8) :
      (((List.range 8).filter fun i ↦
        muNegOneSign σ i == muNegOneSign σ (8 + j)).countP fun i ↦ E i j) = 2 := by
    have hf : ((List.range 8).filter fun i ↦
        muNegOneSign σ i == muNegOneSign σ (8 + j)) =
        ((List.range 8).filter fun (i : Nat) ↦
          decide (su (i : ZMod 8) = sv (j : ZMod 8))) := by
      apply List.filter_congr
      intro i hi
      exact hsame i j (List.mem_range.mp hi) hj
    rw [hf]
    dsimp only [E]
    rw [zmodEight_range_filter_countP_eq_univ_filter_card
      (fun z ↦ decide (su z = sv (j : ZMod 8)))
      (fun z ↦ decide (R.Adj (u z) (v (j : ZMod 8))))]
    simpa [E, and_comm] using (hcross.2 (j : ZMod 8)).1
  have hcolOppEdge (j : Nat) (hj : j < 8) :
      (((List.range 8).filter fun i ↦
        !(muNegOneSign σ i == muNegOneSign σ (8 + j))).countP fun i ↦ E i j) = 1 := by
    have hf : ((List.range 8).filter fun i ↦
        !(muNegOneSign σ i == muNegOneSign σ (8 + j))) =
        ((List.range 8).filter fun (i : Nat) ↦
          decide (su (i : ZMod 8) ≠ sv (j : ZMod 8))) := by
      apply List.filter_congr
      intro i hi
      exact hopp i j (List.mem_range.mp hi) hj
    rw [hf]
    dsimp only [E]
    rw [zmodEight_range_filter_countP_eq_univ_filter_card
      (fun z ↦ decide (su z ≠ sv (j : ZMod 8)))
      (fun z ↦ decide (R.Adj (u z) (v (j : ZMod 8))))]
    simpa [E, ne_eq, and_comm] using (hcross.2 (j : ZMod 8)).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    exact muNegOne_crossComplement_row_count (E i)
      (fun j ↦ muNegOneSign σ i == muNegOneSign σ (8 + j))
      (h305Sign_row_same_length_four σ i hi) (hrowSameEdge i hi)
  · intro i hi
    exact countP_not_eq_three_of_class_four_of_pos_one (List.range 8)
      (fun j ↦ !(muNegOneSign σ i == muNegOneSign σ (8 + j)))
      (E i)
      (h305Sign_row_opp_length_four σ i hi) (hrowOppEdge i hi)
  · intro j hj
    exact muNegOne_crossComplement_col_count (fun i ↦ E i j)
      (fun i ↦ muNegOneSign σ i == muNegOneSign σ (8 + j))
      (h305Sign_col_same_length_four σ j hj) (hcolSameEdge j hj)
  · intro j hj
    exact countP_not_eq_three_of_class_four_of_pos_one (List.range 8)
      (fun i ↦ !(muNegOneSign σ i == muNegOneSign σ (8 + j)))
      (fun i ↦ E i j)
      (h305Sign_col_opp_length_four σ j hj) (hcolOppEdge j hj)


end Erdos85

#print axioms Erdos85.muNegThreeZeroFive_crossDefect_count_fields
