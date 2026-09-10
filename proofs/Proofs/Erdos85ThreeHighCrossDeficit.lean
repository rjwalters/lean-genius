import Proofs.Erdos85ThreeHighCrossCapacity

namespace Erdos85

def threeHighUnassignedRows (k : ℕ) : Finset (Fin 15) :=
  Finset.univ.filter fun i => k ≤ i.val

/-- Remaining U rows must be numerous enough to complete every R degree. -/
def threeHighCrossCanFill (RAdj : Fin 8 → Fin 8 → Bool)
    (partialCross : ThreeHighCross) (k : ℕ) : Bool :=
  decide (∀ j, 4 ≤ encodedRowDegree (fun i => partialCross i j) +
    encodedRowDegree (RAdj j) + (if j.val < 6 then 1 else 0) +
      (threeHighUnassignedRows k).card)

theorem threeHighCrossPrefix_column_bound (cross : ThreeHighCross) (k : ℕ) (j : Fin 8) :
    encodedRowDegree (fun i => cross i j) ≤
      encodedRowDegree (fun i => threeHighCrossPrefix cross k i j) +
        (threeHighUnassignedRows k).card := by
  have hs : (Finset.univ.filter fun i => cross i j) ⊆
      (Finset.univ.filter fun i => threeHighCrossPrefix cross k i j) ∪
        threeHighUnassignedRows k := by
    intro i hi
    have htrue := (Finset.mem_filter.mp hi).2
    by_cases hik : i.val < k
    · apply Finset.mem_union_left
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        threeHighCrossPrefix, if_pos hik]
      exact htrue
    · apply Finset.mem_union_right
      simp only [threeHighUnassignedRows, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

attribute [local irreducible] threeHighCrossDomain encodedC4Free encodedDegreeProfile

theorem threeHighCrossDomain_prefix_canFill
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain UAdj RAdj) (k : ℕ) :
    threeHighCrossCanFill RAdj (threeHighCrossPrefix cross k) k = true := by
  simp only [threeHighCrossCanFill, decide_eq_true_eq]
  intro j
  have hmargin := (threeHighCrossDomain_margins UAdj RAdj cross hc).2 j
  have hbound := threeHighCrossPrefix_column_bound cross k j
  omega

theorem threeHighCrossCanFill_reject
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (k : ℕ)
    (hbad : threeHighCrossCanFill RAdj (threeHighCrossPrefix cross k) k = false) :
    cross ∉ threeHighCrossDomain UAdj RAdj := by
  intro hc
  have h := threeHighCrossDomain_prefix_canFill UAdj RAdj cross hc k
  rw [hbad] at h
  contradiction

end Erdos85
#print axioms Erdos85.threeHighCrossPrefix_column_bound
#print axioms Erdos85.threeHighCrossDomain_prefix_canFill
#print axioms Erdos85.threeHighCrossCanFill_reject
