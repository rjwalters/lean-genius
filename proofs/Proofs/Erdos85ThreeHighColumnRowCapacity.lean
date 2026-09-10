import Proofs.Erdos85ThreeHighColumnDFS
import Proofs.Erdos85ThreeHighCrossCapacity

namespace Erdos85

private theorem suffix_card (k : Nat) :
    (Finset.univ.filter fun j : Fin 8 => k ≤ j.val).card = 8 - k := by
  by_cases hk : k ≤ 8
  · interval_cases k <;> decide
  · have he : (Finset.univ.filter fun j : Fin 8 => k ≤ j.val) = ∅ := by
      ext j
      have hj : ¬ k ≤ j.val := by omega
      simp [hj]
    rw [he,Finset.card_empty]
    omega

theorem encodedRowDegree_column_prefix_bounds (B : Fin 8 → Bool) (k : Nat) :
    encodedRowDegree (fun j => if j.val < k then B j else false) ≤ encodedRowDegree B ∧
      encodedRowDegree B ≤
        encodedRowDegree (fun j => if j.val < k then B j else false) + (8-k) := by
  constructor
  · apply encodedRowDegree_mono
    intro j h
    split at h
    · exact h
    · cases h
  · have hs : (Finset.univ.filter fun j : Fin 8 => B j) ⊆
        (Finset.univ.filter fun j => if j.val < k then B j else false) ∪
          (Finset.univ.filter fun j => k ≤ j.val) := by
      intro j hj
      have hB := (Finset.mem_filter.mp hj).2
      by_cases h : j.val < k
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [if_pos h] using hB⟩
      · apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
    have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
    simpa only [suffix_card,encodedRowDegree] using hc

/-- A column prefix cannot overfill a U row or leave more missing neighbors
than the number of columns still unassigned. -/
def threeHighColumnRowCapacityFor (degrees : Fin 15 → Nat)
    (partialCross : ThreeHighCross) (k : Nat) : Bool :=
  decide (∀ i, degrees i + encodedRowDegree (partialCross i) ≤ 4 ∧
    4 ≤ degrees i + encodedRowDegree (partialCross i) + (8-k))

def threeHighColumnRowCapacity (U : Fin 15 → Fin 15 → Bool)
    (partialCross : ThreeHighCross) (k : Nat) : Bool :=
  threeHighColumnRowCapacityFor (fun i => encodedRowDegree (U i)) partialCross k

attribute [local irreducible] threeHighCrossDomain

theorem threeHighCrossDomain_column_prefix_capacity
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R) (k : Nat) :
    threeHighColumnRowCapacity U (threeHighCrossColumnPrefix cross k) k = true := by
  simp only [threeHighColumnRowCapacity,threeHighColumnRowCapacityFor,decide_eq_true_eq]
  intro i
  have hm := (threeHighCrossDomain_margins U R cross hc).1 i
  have hb := encodedRowDegree_column_prefix_bounds (cross i) k
  change encodedRowDegree (U i) + encodedRowDegree (fun j => if j.val < k then cross i j else false) ≤ 4 ∧
    4 ≤ encodedRowDegree (U i) + encodedRowDegree (fun j => if j.val < k then cross i j else false) + (8-k)
  omega

end Erdos85
#print axioms Erdos85.encodedRowDegree_column_prefix_bounds
#print axioms Erdos85.threeHighCrossDomain_column_prefix_capacity
