import Proofs.Erdos85MuNegOneOneFourEnrichedCapstone
import Proofs.Erdos85MuNegOneOneFourZModCountEnumeration

/-!
# Cross-count fields for the `mu=-1`, `(1,4)` finite semantics

Node: outline F.3, graph-to-finite-semantics instantiation (3c-i).

This file finishes the purely finite plumbing from the exterior graph's
signed `2+2` split to the four row/column count fields of
`MuNegOneOneFourFiniteSemantics`.
-/

namespace Erdos85

private theorem muNegOneSign_row_same_length_four
    (σ : Bool) (i : Nat) (hi : i < 8) :
    ((List.range 8).filter fun j ↦
      muNegOneSign σ i == muNegOneSign σ (8 + j)).length = 4 := by
  cases σ <;> interval_cases i <;> decide

private theorem muNegOneSign_row_opp_length_four
    (σ : Bool) (i : Nat) (hi : i < 8) :
    ((List.range 8).filter fun j ↦
      !(muNegOneSign σ i == muNegOneSign σ (8 + j))).length = 4 := by
  cases σ <;> interval_cases i <;> decide

private theorem muNegOneSign_col_same_length_four
    (σ : Bool) (j : Nat) (hj : j < 8) :
    ((List.range 8).filter fun i ↦
      muNegOneSign σ i == muNegOneSign σ (8 + j)).length = 4 := by
  cases σ <;> interval_cases j <;> decide

private theorem muNegOneSign_col_opp_length_four
    (σ : Bool) (j : Nat) (hj : j < 8) :
    ((List.range 8).filter fun i ↦
      !(muNegOneSign σ i == muNegOneSign σ (8 + j))).length = 4 := by
  cases σ <;> interval_cases j <;> decide

/-- The four cross-defect count fields required by the finite semantics.
`D` is the complement of the exterior-pair graph on the ordered cross block. -/
theorem muNegOneOneFour_crossDefect_count_fields
    {X : Type*} (R : SimpleGraph X) [DecidableRel R.Adj]
    (u v : ZMod 8 → X) (su sv : ZMod 8 → ℤ)
    (hsu : ∀ i, su i = -1 ∨ su i = 1)
    (hsv : ∀ j, sv j = -1 ∨ sv j = 1)
    (hphase : MuNegOneOneFourAlternatingSignPhases su sv)
    (hcross : MuNegOneOneFourCrossExteriorSplit R u v su sv) :
    let σ := muNegOneSigmaOf su sv
    let D : Nat → Nat → Bool := fun i j ↦
      !(decide (R.Adj (u (i : ZMod 8)) (v (j : ZMod 8))))
    (∀ i, i < 8 →
      (((List.range 8).filter fun j ↦
        muNegOneSign σ i == muNegOneSign σ (8 + j)).countP fun j ↦ D i j) = 2) ∧
    (∀ i, i < 8 →
      (((List.range 8).filter fun j ↦
        !(muNegOneSign σ i == muNegOneSign σ (8 + j))).countP fun j ↦ D i j) = 2) ∧
    (∀ j, j < 8 →
      (((List.range 8).filter fun i ↦
        muNegOneSign σ i == muNegOneSign σ (8 + j)).countP fun i ↦ D i j) = 2) ∧
    (∀ j, j < 8 →
      (((List.range 8).filter fun i ↦
        !(muNegOneSign σ i == muNegOneSign σ (8 + j))).countP fun i ↦ D i j) = 2) := by
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
        !(muNegOneSign σ i == muNegOneSign σ (8 + j))).countP fun j ↦ E i j) = 2 := by
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
        !(muNegOneSign σ i == muNegOneSign σ (8 + j))).countP fun i ↦ E i j) = 2 := by
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
      (muNegOneSign_row_same_length_four σ i hi) (hrowSameEdge i hi)
  · intro i hi
    exact muNegOne_crossComplement_row_count (E i)
      (fun j ↦ !(muNegOneSign σ i == muNegOneSign σ (8 + j)))
      (muNegOneSign_row_opp_length_four σ i hi) (hrowOppEdge i hi)
  · intro j hj
    exact muNegOne_crossComplement_col_count (fun i ↦ E i j)
      (fun i ↦ muNegOneSign σ i == muNegOneSign σ (8 + j))
      (muNegOneSign_col_same_length_four σ j hj) (hcolSameEdge j hj)
  · intro j hj
    exact muNegOne_crossComplement_col_count (fun i ↦ E i j)
      (fun i ↦ !(muNegOneSign σ i == muNegOneSign σ (8 + j)))
      (muNegOneSign_col_opp_length_four σ j hj) (hcolOppEdge j hj)

end Erdos85

#print axioms Erdos85.muNegOneOneFour_crossDefect_count_fields
