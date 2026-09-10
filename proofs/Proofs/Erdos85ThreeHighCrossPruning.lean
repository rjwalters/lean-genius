import Proofs.Erdos85EncodedC4Pruning
import Proofs.Erdos85ThreeHighCrossDomain

namespace Erdos85

theorem threeHighEmptyAdj_subgraph
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (partialCross cross : ThreeHighCross)
    (hsub : ∀ i j, partialCross i j = true → cross i j = true) :
    EncodedSubgraph (threeHighEmptyAdj UAdj RAdj partialCross)
      (threeHighEmptyAdj UAdj RAdj cross) := by
  intro p q hp
  unfold threeHighEmptyAdj at hp ⊢
  generalize threeHighEmptySplit p = sp at hp ⊢
  generalize threeHighEmptySplit q = sq at hp ⊢
  rcases sp with (i | j) | r <;> rcases sq with (i' | j') | r' <;>
    simp only at hp ⊢
  all_goals first | exact hp | exact hsub _ _ hp

/-- Keep the first k incidence rows; later rows have no edges yet. -/
def threeHighCrossPrefix (cross : ThreeHighCross) (k : ℕ) : ThreeHighCross :=
  fun i j => if i.val < k then cross i j else false

attribute [local irreducible] threeHighCrossDomain encodedC4Free

theorem threeHighCrossDomain_prefix_c4
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain UAdj RAdj)
    (k : ℕ) :
    encodedC4Free (threeHighEmptyAdj UAdj RAdj (threeHighCrossPrefix cross k)) = true := by
  apply encodedC4Free_of_subgraph _ (threeHighEmptyAdj UAdj RAdj cross)
  · apply threeHighEmptyAdj_subgraph
    intro i j h
    by_cases hi : i.val < k
    · simpa only [threeHighCrossPrefix, if_pos hi] using h
    · simp only [threeHighCrossPrefix, if_neg hi, Bool.false_eq_true] at h
  · exact ((mem_threeHighCrossDomain_iff UAdj RAdj cross).mp hc).1

theorem threeHighCrossPrefix_reject
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (k : ℕ)
    (hbad : encodedC4Free
      (threeHighEmptyAdj UAdj RAdj (threeHighCrossPrefix cross k)) = false) :
    cross ∉ threeHighCrossDomain UAdj RAdj := by
  intro hc
  have h := threeHighCrossDomain_prefix_c4 UAdj RAdj cross hc k
  rw [hbad] at h
  contradiction

end Erdos85
#print axioms Erdos85.threeHighEmptyAdj_subgraph
#print axioms Erdos85.threeHighCrossDomain_prefix_c4
#print axioms Erdos85.threeHighCrossPrefix_reject
