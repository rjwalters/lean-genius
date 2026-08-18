import Proofs.Erdos85OrderSixtyFourMuThreeSignCensus

/-! # Joint colored-order and mu-three terminal for lambda-six blocks -/

namespace Erdos85

/-- The exact `(triangle-free colored order, μ=3 multiplicity)` records that
survive the local parity screen in the `[10,6]` and `[5,5,3,3]` lambda-six
strata. -/
def IsLambdaSixColoredRecord (coloredOrder muThreeMultiplicity : ℕ) : Prop :=
  (coloredOrder = 0 ∧ muThreeMultiplicity = 0) ∨
  (coloredOrder = 6 ∧ muThreeMultiplicity = 1) ∨
  (coloredOrder = 10 ∧ muThreeMultiplicity = 1) ∨
  (coloredOrder = 16 ∧ muThreeMultiplicity = 0) ∨
  (coloredOrder = 16 ∧ muThreeMultiplicity = 1)

/-- Four locally valid lambda-six records whose colored orders sum to
sixteen have total `μ=3` multiplicity at most two. -/
theorem four_lambdaSixColoredRecords_muThreeMultiplicity_le_two
    (o₀ o₁ o₂ o₃ m₀ m₁ m₂ m₃ : ℕ)
    (h₀ : IsLambdaSixColoredRecord o₀ m₀)
    (h₁ : IsLambdaSixColoredRecord o₁ m₁)
    (h₂ : IsLambdaSixColoredRecord o₂ m₂)
    (h₃ : IsLambdaSixColoredRecord o₃ m₃)
    (horder : o₀ + o₁ + o₂ + o₃ = 16) :
    m₀ + m₁ + m₂ + m₃ ≤ 2 := by
  rcases h₀ with h₀ | h₀ | h₀ | h₀ | h₀ <;>
    rcases h₁ with h₁ | h₁ | h₁ | h₁ | h₁ <;>
    rcases h₂ with h₂ | h₂ | h₂ | h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ | h₃ | h₃ | h₃ <;> omega

/-- Hence the lambda-six joint colored-order screen contradicts the global
sign census, which requires total `μ=3` multiplicity at least four. -/
theorem false_of_four_lambdaSixColoredRecords_of_muThreeMultiplicity_ge_four
    (o₀ o₁ o₂ o₃ m₀ m₁ m₂ m₃ : ℕ)
    (h₀ : IsLambdaSixColoredRecord o₀ m₀)
    (h₁ : IsLambdaSixColoredRecord o₁ m₁)
    (h₂ : IsLambdaSixColoredRecord o₂ m₂)
    (h₃ : IsLambdaSixColoredRecord o₃ m₃)
    (horder : o₀ + o₁ + o₂ + o₃ = 16)
    (hmult : 4 ≤ m₀ + m₁ + m₂ + m₃) : False := by
  have hle := four_lambdaSixColoredRecords_muThreeMultiplicity_le_two
    o₀ o₁ o₂ o₃ m₀ m₁ m₂ m₃ h₀ h₁ h₂ h₃ horder
  omega

private theorem sum_fin_four (f : Fin 4 → ℕ) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 := by
  simp [Fin.sum_univ_succ, add_assoc]

/-- Component-indexed form used by the graph-level four-component
assembly. -/
theorem false_of_finFour_lambdaSixColoredRecords
    (coloredOrder muThreeMultiplicity : Fin 4 → ℕ)
    (hrecord : ∀ i, IsLambdaSixColoredRecord
      (coloredOrder i) (muThreeMultiplicity i))
    (horder : ∑ i, coloredOrder i = 16)
    (hmult : 4 ≤ ∑ i, muThreeMultiplicity i) : False := by
  rw [sum_fin_four] at horder hmult
  exact false_of_four_lambdaSixColoredRecords_of_muThreeMultiplicity_ge_four
    (coloredOrder 0) (coloredOrder 1) (coloredOrder 2) (coloredOrder 3)
    (muThreeMultiplicity 0) (muThreeMultiplicity 1)
    (muThreeMultiplicity 2) (muThreeMultiplicity 3)
    (hrecord 0) (hrecord 1) (hrecord 2) (hrecord 3) horder hmult

/-- Equivalence-invariant form for an arbitrary four-element component
index type. -/
theorem false_of_card_four_lambdaSixColoredRecords
    {C : Type*} [Fintype C] [DecidableEq C]
    (hcard : Fintype.card C = 4)
    (coloredOrder muThreeMultiplicity : C → ℕ)
    (hrecord : ∀ c, IsLambdaSixColoredRecord
      (coloredOrder c) (muThreeMultiplicity c))
    (horder : ∑ c, coloredOrder c = 16)
    (hmult : 4 ≤ ∑ c, muThreeMultiplicity c) : False := by
  let e : C ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  apply false_of_finFour_lambdaSixColoredRecords
    (fun i => coloredOrder (e.symm i))
    (fun i => muThreeMultiplicity (e.symm i))
  · intro i
    exact hrecord (e.symm i)
  · rw [Equiv.sum_comp e.symm]
    exact horder
  · rw [Equiv.sum_comp e.symm]
    exact hmult

end Erdos85
