import Mathlib

/-! # Exact diagonal supports in the `mu=-1`, `(k,r)=(1,4)` self cell

Node: `SIZE-TWO-EIGENLINE(q)` beneath outline F.3.

The diagonal row has size three and contains the antipode.  If the two cycle
entries occur, they exhaust the row.  If they vanish, looplessness and the
offset-two common-neighbor obstruction leave exactly offsets `±3` beside the
antipode.  The lemmas below isolate the finite `ZMod 8` kernel from the graph
consumer.
-/

open Finset

namespace Erdos85

noncomputable section

/-- A three-element normalized row containing offsets `1,4,7` has exactly
that support. -/
theorem zmodEight_rowThree_cycleOne_four_iff
    (R : ZMod 8 → Prop) [DecidablePred R]
    (hcard : ((Finset.univ : Finset (ZMod 8)).filter R).card = 3)
    (h1 : R 1) (h4 : R 4) (h7 : R 7) :
    ∀ j, R j ↔ j = 1 ∨ j = 4 ∨ j = 7 := by
  let T := (Finset.univ : Finset (ZMod 8)).filter R
  let S : Finset (ZMod 8) := {1, 4, 7}
  have hScard : S.card = 3 := by decide
  have hTcard : T.card = 3 := by simpa [T] using hcard
  have hsub : S ⊆ T := by
    intro j hj
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> simp [T, h1, h4, h7]
  have heq : S = T :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro j
  have hmemT : j ∈ T ↔ R j := by simp [T]
  have hmemS : j ∈ S ↔ j = 1 ∨ j = 4 ∨ j = 7 := by simp [S]
  rw [← hmemT, ← heq, hmemS]

/-- A three-element normalized row avoiding offsets `0,±1,±2` and containing
the antipode has exactly support `{±3,4}`. -/
theorem zmodEight_rowThree_cycleZero_four_iff
    (R : ZMod 8 → Prop) [DecidablePred R]
    (hcard : ((Finset.univ : Finset (ZMod 8)).filter R).card = 3)
    (h0 : ¬ R 0) (h1 : ¬ R 1) (h2 : ¬ R 2) (h4 : R 4)
    (h6 : ¬ R 6) (h7 : ¬ R 7) :
    ∀ j, R j ↔ j = 3 ∨ j = 4 ∨ j = 5 := by
  let T := (Finset.univ : Finset (ZMod 8)).filter R
  let S : Finset (ZMod 8) := {3, 4, 5}
  have hTcard : T.card = 3 := by simpa [T] using hcard
  have hScard : S.card = 3 := by decide
  have hsub : T ⊆ S := by
    intro j hj
    have hR : R j := (Finset.mem_filter.mp hj).2
    rw [show j ∈ S ↔ j = 3 ∨ j = 4 ∨ j = 5 by simp [S]]
    have hall : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨
        j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by
      exact (by decide : ∀ j : ZMod 8,
        j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨
          j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) j
    rcases hall with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim (h0 hR)
    · exact False.elim (h1 hR)
    · exact False.elim (h2 hR)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact False.elim (h6 hR)
    · exact False.elim (h7 hR)
  have heq : T = S :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hTcard, hScard])
  intro j
  have hmemT : j ∈ T ↔ R j := by simp [T]
  have hmemS : j ∈ S ↔ j = 3 ∨ j = 4 ∨ j = 5 := by simp [S]
  rw [← hmemT, heq, hmemS]

private theorem zmodEight_translated_row_card
    (R : ZMod 8 → ZMod 8 → Prop) [DecidableRel R]
    (i : ZMod 8) (n : ℕ)
    (hcard : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ R i j).card = n) :
    ((Finset.univ : Finset (ZMod 8)).filter fun d ↦ R i (i + d)).card = n := by
  let T := (Finset.univ : Finset (ZMod 8)).filter fun d ↦ R i (i + d)
  let U := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ R i j
  have hTU : T.card = U.card := by
    apply Finset.card_bij (fun d _ ↦ i + d)
    · intro d hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hd).2⟩
    · intro d₁ hd₁ d₂ hd₂ heq
      exact add_left_cancel heq
    · intro j hj
      refine ⟨j - i, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          have hij : i + (j - i) = j := by ring
          simpa [hij] using (Finset.mem_filter.mp hj).2⟩
      · ring
  rw [hTU]
  simpa [U] using hcard

/-- Translated row form of the all-triangle-free support `{±1,4}`. -/
theorem zmodEight_rowsThree_cycleOne_four_sub_iff
    (R : ZMod 8 → ZMod 8 → Prop) [DecidableRel R]
    (hcard : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ R i j).card = 3)
    (h1 : ∀ i, R i (i + 1)) (h4 : ∀ i, R i (i + 4))
    (h7 : ∀ i, R i (i + 7)) :
    ∀ i j, R i j ↔ j - i = 1 ∨ j - i = 4 ∨ j - i = 7 := by
  intro i j
  have hc := zmodEight_translated_row_card R i 3 (hcard i)
  have hk := zmodEight_rowThree_cycleOne_four_iff
    (fun d ↦ R i (i + d)) hc (h1 i) (h4 i) (h7 i) (j - i)
  have hij : i + (j - i) = j := by ring
  simpa [hij] using hk

/-- Translated row form of the all-triangle support `{±3,4}`. -/
theorem zmodEight_rowsThree_cycleZero_four_sub_iff
    (R : ZMod 8 → ZMod 8 → Prop) [DecidableRel R]
    (hcard : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ R i j).card = 3)
    (h0 : ∀ i, ¬ R i i)
    (h1 : ∀ i, ¬ R i (i + 1)) (h2 : ∀ i, ¬ R i (i + 2))
    (h4 : ∀ i, R i (i + 4))
    (h6 : ∀ i, ¬ R i (i + 6)) (h7 : ∀ i, ¬ R i (i + 7)) :
    ∀ i j, R i j ↔ j - i = 3 ∨ j - i = 4 ∨ j - i = 5 := by
  intro i j
  have hc := zmodEight_translated_row_card R i 3 (hcard i)
  have hk := zmodEight_rowThree_cycleZero_four_iff
    (fun d ↦ R i (i + d)) hc (by simpa using h0 i) (h1 i) (h2 i) (h4 i)
      (h6 i) (h7 i) (j - i)
  have hij : i + (j - i) = j := by ring
  simpa [hij] using hk

end


end Erdos85

#print axioms Erdos85.zmodEight_rowThree_cycleOne_four_iff
#print axioms Erdos85.zmodEight_rowThree_cycleZero_four_iff
#print axioms Erdos85.zmodEight_rowsThree_cycleOne_four_sub_iff
#print axioms Erdos85.zmodEight_rowsThree_cycleZero_four_sub_iff
