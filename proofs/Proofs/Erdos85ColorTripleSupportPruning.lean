import Proofs.Erdos85OrderFortyNineThreeHighTripleColorFamilyCompatibility

namespace Erdos85

/-- Simultaneous support filtering uses the previous lists for every color. -/
def threeHighTripleSupportPass (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) (i : Fin 3) : List (Finset (Fin 24)) :=
  (D i).filter fun S => (List.finRange 3).all fun j =>
    decide (i = j) || (D j).any (fun T => encodedCrossIndependent B S T)

theorem threeHighTripleSupportPass_preserves
    (B : Fin 24 → Fin 24 → Bool) (D : Fin 3 → List (Finset (Fin 24)))
    (F : Fin 3 → Finset (Finset (Fin 24)))
    (hmem : ∀ i S, S ∈ F i → S ∈ D i)
    (hcompat : ∀ i j, i ≠ j → encodedFamilyCompatibility B (F i) (F j) = true) :
    ∀ i S, S ∈ F i → S ∈ threeHighTripleSupportPass B D i := by
  intro i S hS
  apply List.mem_filter.mpr
  refine ⟨hmem i S hS, ?_⟩
  apply List.all_eq_true.mpr
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · have h := of_decide_eq_true (hcompat i j hij)
    obtain ⟨T,hT,hST⟩ := h S hS
    have ht : (D j).any (fun T => encodedCrossIndependent B S T) = true :=
      List.any_eq_true.mpr ⟨T,hmem j T hT,hST⟩
    simp [ht]

def threeHighTripleSupportRounds (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) : Nat → Fin 3 → List (Finset (Fin 24))
  | 0 => D
  | n + 1 => threeHighTripleSupportPass B (threeHighTripleSupportRounds B D n)

/-- Any fixed number of passes retains the same compatible family witnesses. -/
theorem threeHighTripleSupportRounds_preserves
    (B : Fin 24 → Fin 24 → Bool) (D : Fin 3 → List (Finset (Fin 24)))
    (F : Fin 3 → Finset (Finset (Fin 24)))
    (hmem : ∀ i S, S ∈ F i → S ∈ D i)
    (hcompat : ∀ i j, i ≠ j → encodedFamilyCompatibility B (F i) (F j) = true)
    (n : Nat) : ∀ i S, S ∈ F i → S ∈ threeHighTripleSupportRounds B D n i := by
  induction n with
  | zero => exact hmem
  | succ n ih => exact threeHighTripleSupportPass_preserves B _ F ih hcompat

end Erdos85
#print axioms Erdos85.threeHighTripleSupportPass_preserves
#print axioms Erdos85.threeHighTripleSupportRounds_preserves
