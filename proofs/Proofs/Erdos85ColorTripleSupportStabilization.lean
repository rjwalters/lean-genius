import Proofs.Erdos85ColorTripleSupportPruning

namespace Erdos85

def threeHighTripleSupportSize (D : Fin 3 → List (Finset (Fin 24))) : Nat :=
  (D 0).length + (D 1).length + (D 2).length

theorem threeHighTripleSupportPass_sublist (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) (i : Fin 3) :
    List.Sublist (threeHighTripleSupportPass B D i) (D i) := List.filter_sublist

private theorem pass_eq_of_size_eq (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24)))
    (h : threeHighTripleSupportSize (threeHighTripleSupportPass B D) =
      threeHighTripleSupportSize D) : threeHighTripleSupportPass B D = D := by
  have h0 := (threeHighTripleSupportPass_sublist B D 0).length_le
  have h1 := (threeHighTripleSupportPass_sublist B D 1).length_le
  have h2 := (threeHighTripleSupportPass_sublist B D 2).length_le
  unfold threeHighTripleSupportSize at h
  have e0 : threeHighTripleSupportPass B D 0 = D 0 :=
    (threeHighTripleSupportPass_sublist B D 0).eq_of_length (by omega)
  have e1 : threeHighTripleSupportPass B D 1 = D 1 :=
    (threeHighTripleSupportPass_sublist B D 1).eq_of_length (by omega)
  have e2 : threeHighTripleSupportPass B D 2 = D 2 :=
    (threeHighTripleSupportPass_sublist B D 2).eq_of_length (by omega)
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

private theorem rounds_shift (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) (n : Nat) :
    threeHighTripleSupportRounds B D (n+1) =
      threeHighTripleSupportRounds B (threeHighTripleSupportPass B D) n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (threeHighTripleSupportPass B) ih

/-- At most one pass per initial list entry suffices to reach an exact list fixed point. -/
theorem threeHighTripleSupportRounds_stable (B : Fin 24 → Fin 24 → Bool)
    (n : Nat) (D : Fin 3 → List (Finset (Fin 24)))
    (hsize : threeHighTripleSupportSize D ≤ n) :
    threeHighTripleSupportPass B (threeHighTripleSupportRounds B D n) =
      threeHighTripleSupportRounds B D n := by
  induction n generalizing D with
  | zero =>
    change threeHighTripleSupportPass B D = D
    apply pass_eq_of_size_eq
    have h0 := (threeHighTripleSupportPass_sublist B D 0).length_le
    have h1 := (threeHighTripleSupportPass_sublist B D 1).length_le
    have h2 := (threeHighTripleSupportPass_sublist B D 2).length_le
    unfold threeHighTripleSupportSize at *
    omega
  | succ n ih =>
    by_cases he : threeHighTripleSupportPass B D = D
    · have hr : ∀ m, threeHighTripleSupportRounds B D m = D := by
        intro m
        induction m with
        | zero => rfl
        | succ m hm => simpa only [threeHighTripleSupportRounds, hm] using he
      simpa only [hr] using he
    · rw [rounds_shift]
      apply ih
      have h0 := (threeHighTripleSupportPass_sublist B D 0).length_le
      have h1 := (threeHighTripleSupportPass_sublist B D 1).length_le
      have h2 := (threeHighTripleSupportPass_sublist B D 2).length_le
      have hne : threeHighTripleSupportSize (threeHighTripleSupportPass B D) ≠
          threeHighTripleSupportSize D := fun h => he (pass_eq_of_size_eq B D h)
      unfold threeHighTripleSupportSize at *
      omega

/-- Once the size bound is reached, every additional pass leaves the lists unchanged. -/
theorem threeHighTripleSupportRounds_add_stable (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) (n m : Nat)
    (hsize : threeHighTripleSupportSize D ≤ n) :
    threeHighTripleSupportRounds B D (n+m) = threeHighTripleSupportRounds B D n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change threeHighTripleSupportPass B (threeHighTripleSupportRounds B D (n+m)) = _
    rw [ih]
    exact threeHighTripleSupportRounds_stable B n D hsize

end Erdos85
#print axioms Erdos85.threeHighTripleSupportPass_sublist
#print axioms Erdos85.threeHighTripleSupportRounds_stable

#print axioms Erdos85.threeHighTripleSupportRounds_add_stable
