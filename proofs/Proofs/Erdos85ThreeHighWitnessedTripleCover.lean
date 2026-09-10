import Proofs.Erdos85ThreeHighSelectedSeparatedCertificate

namespace Erdos85

inductive ThreeHighTripleCoverReason where
  | kept
  | conflict (a b c : Fin 24)
  deriving DecidableEq

def threeHighTripleCoverReasonCheck (B : Fin 24 → Fin 24 → Bool)
    (D : List (Finset (Fin 24))) (S : Finset (Fin 24)) : ThreeHighTripleCoverReason → Bool
  | .kept => decide (S ∈ D)
  | .conflict a b c => decide (a ∈ S ∧ b ∈ S ∧ a ≠ b) && B a c && B b c

theorem threeHighTripleCoverReasonCheck_sound (B : Fin 24 → Fin 24 → Bool)
    (D : List (Finset (Fin 24))) (S : Finset (Fin 24)) (reason : ThreeHighTripleCoverReason)
    (hc : threeHighTripleCoverReasonCheck B D S reason = true)
    (hS : threeHighTripleNoCommonNeighbor B S = true) : S ∈ D := by
  cases reason with
  | kept => exact of_decide_eq_true hc
  | conflict a b c =>
    simp only [threeHighTripleCoverReasonCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hn := of_decide_eq_true hS
    exact False.elim (hn a hc.1.1.1 b hc.1.1.2.1 hc.1.1.2.2 c ⟨hc.1.2,hc.2⟩)

/-- Check one reason per candidate; a short reason list rejects instead of skipping candidates. -/
def threeHighTripleCoverReasonsCheck (B : Fin 24 → Fin 24 → Bool)
    (D : List (Finset (Fin 24))) : List (Finset (Fin 24)) → List ThreeHighTripleCoverReason → Bool
  | [], _ => true
  | _ :: _, [] => false
  | S :: rest, reason :: reasons =>
      threeHighTripleCoverReasonCheck B D S reason && threeHighTripleCoverReasonsCheck B D rest reasons

theorem threeHighTripleCoverReasonsCheck_sound (B : Fin 24 → Fin 24 → Bool)
    (D candidates : List (Finset (Fin 24))) (reasons : List ThreeHighTripleCoverReason)
    (hc : threeHighTripleCoverReasonsCheck B D candidates reasons = true) :
    ∀ S ∈ candidates, threeHighTripleNoCommonNeighbor B S = true → S ∈ D := by
  induction candidates generalizing reasons with
  | nil => simp
  | cons T rest ih =>
    cases reasons with
    | nil => cases hc
    | cons reason reasons =>
      simp only [threeHighTripleCoverReasonsCheck, Bool.and_eq_true] at hc
      intro S hS hn
      rcases List.mem_cons.mp hS with rfl | hS
      · exact threeHighTripleCoverReasonCheck_sound B D S reason hc.1 hn
      · exact ih reasons hc.2 S hS hn

def threeHighWitnessedTripleCoverCheck (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) (reasons : Fin 3 → List ThreeHighTripleCoverReason) : Bool :=
  (List.finRange 3).all fun k =>
    threeHighTripleCoverReasonsCheck B (D k) (threeHighCanonicalTripleShapes k) (reasons k)

theorem threeHighWitnessedTripleCoverCheck_sound (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) (reasons : Fin 3 → List ThreeHighTripleCoverReason)
    (hc : threeHighWitnessedTripleCoverCheck B D reasons = true) :
    threeHighInitialTripleCoverChecked B D = true := by
  apply List.all_eq_true.mpr
  intro k hk
  apply List.all_eq_true.mpr
  intro S hS
  by_cases hn : threeHighTripleNoCommonNeighbor B S = true
  · have hm := threeHighTripleCoverReasonsCheck_sound B (D k) _ (reasons k)
      (List.all_eq_true.mp hc k hk) S hS hn
    simp only [hn, Bool.not_true, Bool.false_or, decide_eq_true_eq]
    exact hm
  · cases h : threeHighTripleNoCommonNeighbor B S <;> simp_all

end Erdos85
#print axioms Erdos85.threeHighTripleCoverReasonCheck_sound
#print axioms Erdos85.threeHighTripleCoverReasonsCheck_sound
#print axioms Erdos85.threeHighWitnessedTripleCoverCheck_sound
