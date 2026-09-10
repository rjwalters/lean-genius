import Proofs.Erdos85ColorTripleSupportStabilization

namespace Erdos85

/-- Stop as soon as a support pass leaves all three ordered lists unchanged. -/
def threeHighTripleSupportUntilStable (B : Fin 24 → Fin 24 → Bool) :
    Nat → (Fin 3 → List (Finset (Fin 24))) → (Fin 3 → List (Finset (Fin 24)))
  | 0, D => D
  | n+1, D =>
    let E := threeHighTripleSupportPass B D
    if E = D then D else threeHighTripleSupportUntilStable B n E

private theorem rounds_of_fixed (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24)))
    (h : threeHighTripleSupportPass B D = D) (n : Nat) :
    threeHighTripleSupportRounds B D n = D := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [threeHighTripleSupportRounds, ih] using h

private theorem rounds_shift (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) (n : Nat) :
    threeHighTripleSupportRounds B D (n+1) =
      threeHighTripleSupportRounds B (threeHighTripleSupportPass B D) n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (threeHighTripleSupportPass B) ih

theorem threeHighTripleSupportUntilStable_eq_rounds (B : Fin 24 → Fin 24 → Bool)
    (n : Nat) (D : Fin 3 → List (Finset (Fin 24))) :
    threeHighTripleSupportUntilStable B n D = threeHighTripleSupportRounds B D n := by
  induction n generalizing D with
  | zero => rfl
  | succ n ih =>
    by_cases h : threeHighTripleSupportPass B D = D
    · simpa only [threeHighTripleSupportUntilStable, h, ite_true] using
        (rounds_of_fixed B D h (n+1)).symm
    · simp only [threeHighTripleSupportUntilStable, h, ite_false, ih, rounds_shift]

/-- A bounded executable closure; the fuel is sufficient even with duplicate entries. -/
def threeHighTripleSupportClosure (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) : Fin 3 → List (Finset (Fin 24)) :=
  threeHighTripleSupportUntilStable B (threeHighTripleSupportSize D) D

theorem threeHighTripleSupportClosure_fixed (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) :
    threeHighTripleSupportPass B (threeHighTripleSupportClosure B D) =
      threeHighTripleSupportClosure B D := by
  unfold threeHighTripleSupportClosure
  rw [threeHighTripleSupportUntilStable_eq_rounds]
  exact threeHighTripleSupportRounds_stable B _ D (Nat.le_refl _)

theorem threeHighTripleSupportClosure_preserves (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) (F : Fin 3 → Finset (Finset (Fin 24)))
    (hmem : ∀ i S, S ∈ F i → S ∈ D i)
    (hcompat : ∀ i j, i ≠ j → encodedFamilyCompatibility B (F i) (F j) = true) :
    ∀ i S, S ∈ F i → S ∈ threeHighTripleSupportClosure B D i := by
  unfold threeHighTripleSupportClosure
  rw [threeHighTripleSupportUntilStable_eq_rounds]
  exact threeHighTripleSupportRounds_preserves B D F hmem hcompat _

end Erdos85
#print axioms Erdos85.threeHighTripleSupportUntilStable_eq_rounds
#print axioms Erdos85.threeHighTripleSupportClosure_fixed
#print axioms Erdos85.threeHighTripleSupportClosure_preserves
