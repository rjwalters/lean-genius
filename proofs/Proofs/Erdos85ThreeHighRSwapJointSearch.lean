import Proofs.Erdos85ThreeHighRSwapOrdering
import Proofs.Erdos85ThreeHighJointExternalSearch

namespace Erdos85
attribute [local irreducible] threeHighCrossDomain

/-- Validate a caller-supplied list once, outside cross enumeration. -/
def threeHighRSwapPairsValid (R : Fin 8 → Fin 8 → Bool)
    (pairs : List (Fin 8 × Fin 8)) : Bool :=
  decide (pairs.Pairwise (fun p q => p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2)) &&
    pairs.all (fun p => decide (∀ j, (Equiv.swap p.1 p.2 j).val < 6 ↔ j.val < 6)) &&
    pairs.all (fun p => decide (∀ i j, R (Equiv.swap p.1 p.2 i) (Equiv.swap p.1 p.2 j) = R i j))

def threeHighRSwapOrdered (pairs : List (Fin 8 × Fin 8))
    (score : (Fin 15 → Bool) → Nat) (cross : ThreeHighCross) : Bool :=
  pairs.all fun p => decide (score (fun i => cross i p.1) ≤ score (fun i => cross i p.2))

/-- Binary column score; injectivity is unnecessary for ordering completeness. -/
def threeHighColumnScore (column : Fin 15 → Bool) : Nat :=
  (List.finRange 15).foldl (fun n i => n + if column i then 2 ^ i.val else 0) 0

theorem threeHighRSwapOrdered_complete
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (pairs : List (Fin 8 × Fin 8)) (score : (Fin 15 → Bool) → Nat)
    (hv : threeHighRSwapPairsValid R pairs = true)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true)
    (hj : ThreeHighJointWitness (threeHighEmptyAdj U R cross)) :
    ∃ c : ThreeHighCross, c ∈ threeHighCrossDomain U R ∧
      encodedExternalBlockCap (threeHighEmptyAdj U R c) threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj U R c) ∧
      threeHighRSwapOrdered pairs score c = true := by
  simp only [threeHighRSwapPairsValid,Bool.and_eq_true,decide_eq_true_eq] at hv
  have hn := fun p hp => of_decide_eq_true (List.all_eq_true.mp hv.1.2 p hp)
  have hr := fun p hp => of_decide_eq_true (List.all_eq_true.mp hv.2 p hp)
  obtain ⟨c,hc',he',hj',ho,_⟩ := threeHighRDisjointSwaps_ordered_witness
    U R pairs score hv.1.1 hn hr cross hc he hj
  refine ⟨c,hc',he',hj',?_⟩
  exact List.all_eq_true.mpr (fun p hp => decide_eq_true (ho p hp))

/-- Reject unordered orbit mates before invoking the terminal predicate.
Invalid swap data selects the ordinary search, preserving completeness. -/
def threeHighRSwapJointSearch (pairs : List (Fin 8 × Fin 8))
    (score : (Fin 15 → Bool) → Nat) (search : ThreeHighExternalSearch)
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) : ThreeHighJointExternalSearch :=
  fun U R =>
    if threeHighRSwapPairsValid R pairs then
      search U R (fun c => threeHighRSwapOrdered pairs score c && accept (threeHighEmptyAdj U R c))
    else search U R (fun c => accept (threeHighEmptyAdj U R c))

theorem threeHighRSwapJointSearch_sound (pairs : List (Fin 8 × Fin 8))
    (score : (Fin 15 → Bool) → Nat) (search : ThreeHighExternalSearch)
    (hs : ThreeHighExternalSearchSound search)
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (ha : ThreeHighTerminalSound accept) :
    ThreeHighJointExternalSearchSound (threeHighRSwapJointSearch pairs score search accept) := by
  intro U R cross hc he hj
  simp only [threeHighRSwapJointSearch]
  split
  · rename_i hv
    obtain ⟨c,hc',he',hj',ho⟩ := threeHighRSwapOrdered_complete U R pairs score hv cross hc he hj
    apply hs U R _ c hc' he'
    simp only [ho,ha _ hj',Bool.and_self]
  · exact hs U R _ cross hc he (ha _ hj)

end Erdos85
#print axioms Erdos85.threeHighRSwapOrdered_complete
#print axioms Erdos85.threeHighRSwapJointSearch_sound
