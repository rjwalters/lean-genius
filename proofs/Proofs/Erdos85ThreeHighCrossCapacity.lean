import Proofs.Erdos85ThreeHighCrossMargins
import Proofs.Erdos85ThreeHighCrossPruning

namespace Erdos85

theorem encodedRowDegree_mono {W : Type*} [Fintype W]
    (A B : W → Bool) (h : ∀ x, A x = true → B x = true) :
    encodedRowDegree A ≤ encodedRowDegree B := by
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact h x hx

/-- A partially assigned U-R matrix must not overfill any R vertex. -/
def threeHighCrossCapacity (RAdj : Fin 8 → Fin 8 → Bool)
    (partialCross : ThreeHighCross) : Bool :=
  decide (∀ j, encodedRowDegree (fun i => partialCross i j) + encodedRowDegree (RAdj j) +
    (if j.val < 6 then 1 else 0) ≤ 4)

attribute [local irreducible] threeHighCrossDomain encodedC4Free encodedDegreeProfile

theorem threeHighCrossDomain_partial_capacity
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (partialCross cross : ThreeHighCross)
    (hsub : ∀ i j, partialCross i j = true → cross i j = true)
    (hc : cross ∈ threeHighCrossDomain UAdj RAdj) :
    threeHighCrossCapacity RAdj partialCross = true := by
  simp only [threeHighCrossCapacity, decide_eq_true_eq]
  intro j
  have hm := (threeHighCrossDomain_margins UAdj RAdj cross hc).2 j
  have hle := encodedRowDegree_mono (fun i => partialCross i j) (fun i => cross i j)
    (fun i => hsub i j)
  omega

theorem threeHighCrossDomain_prefix_capacity
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain UAdj RAdj) (k : ℕ) :
    threeHighCrossCapacity RAdj (threeHighCrossPrefix cross k) = true := by
  apply threeHighCrossDomain_partial_capacity UAdj RAdj _ cross _ hc
  intro i j h
  by_cases hi : i.val < k
  · simpa only [threeHighCrossPrefix, if_pos hi] using h
  · simp only [threeHighCrossPrefix, if_neg hi, Bool.false_eq_true] at h

theorem threeHighCrossCapacity_reject_extension
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (partialCross cross : ThreeHighCross)
    (hsub : ∀ i j, partialCross i j = true → cross i j = true)
    (hbad : threeHighCrossCapacity RAdj partialCross = false) :
    cross ∉ threeHighCrossDomain UAdj RAdj := by
  intro hc
  have h := threeHighCrossDomain_partial_capacity UAdj RAdj partialCross cross hsub hc
  rw [hbad] at h
  contradiction

end Erdos85
#print axioms Erdos85.encodedRowDegree_mono
#print axioms Erdos85.threeHighCrossDomain_partial_capacity
#print axioms Erdos85.threeHighCrossDomain_prefix_capacity
#print axioms Erdos85.threeHighCrossCapacity_reject_extension
