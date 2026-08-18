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

end Erdos85
