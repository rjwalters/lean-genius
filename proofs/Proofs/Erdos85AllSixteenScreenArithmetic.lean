import Proofs.Erdos85LambdaSixColoredOrderTerminal

/-! # Arithmetic interface for the full size-two component screen -/

namespace Erdos85

/-- Compact record set containing exactly the locally valid colored-order
and `μ=3` multiplicity pairs from the `[16]`, `[10,6]`, and `[5,5,3,3]`
screens.  For order zero or sixteen the exact multiplicity may be `0,1,2`;
the mixed-cycle orders six and ten have multiplicity exactly one. -/
def IsSizeTwoScreenRecord (coloredOrder muThreeMultiplicity : ℕ) : Prop :=
  ((coloredOrder = 0 ∨ coloredOrder = 16) ∧ muThreeMultiplicity ≤ 2) ∨
  (coloredOrder = 6 ∧ muThreeMultiplicity = 1) ∨
  (coloredOrder = 10 ∧ muThreeMultiplicity = 1)

theorem sizeTwoScreenRecord_muThreeMultiplicity_le_two
    {o m : ℕ} (h : IsSizeTwoScreenRecord o m) : m ≤ 2 := by
  rcases h with h | h | h <;> omega

theorem sizeTwoScreenRecord_order_six_or_ten_muThreeMultiplicity_eq_one
    {o m : ℕ} (h : IsSizeTwoScreenRecord o m)
    (ho : o = 6 ∨ o = 10) : m = 1 := by
  rcases h with h | h | h <;> omega

/-- If four screened colored orders sum to sixteen, either one component
has colored order sixteen, or both exceptional orders ten and six occur.
These are precisely the global patterns `16+0+0+0` and `10+6+0+0`. -/
theorem four_sizeTwoScreenRecords_coloredOrder_pattern
    (o₀ o₁ o₂ o₃ m₀ m₁ m₂ m₃ : ℕ)
    (h₀ : IsSizeTwoScreenRecord o₀ m₀)
    (h₁ : IsSizeTwoScreenRecord o₁ m₁)
    (h₂ : IsSizeTwoScreenRecord o₂ m₂)
    (h₃ : IsSizeTwoScreenRecord o₃ m₃)
    (horder : o₀ + o₁ + o₂ + o₃ = 16) :
    (o₀ = 16 ∨ o₁ = 16 ∨ o₂ = 16 ∨ o₃ = 16) ∨
      ((o₀ = 10 ∨ o₁ = 10 ∨ o₂ = 10 ∨ o₃ = 10) ∧
       (o₀ = 6 ∨ o₁ = 6 ∨ o₂ = 6 ∨ o₃ = 6)) := by
  have ho₀ : o₀ = 0 ∨ o₀ = 6 ∨ o₀ = 10 ∨ o₀ = 16 := by
    rcases h₀ with h | h | h <;> omega
  have ho₁ : o₁ = 0 ∨ o₁ = 6 ∨ o₁ = 10 ∨ o₁ = 16 := by
    rcases h₁ with h | h | h <;> omega
  have ho₂ : o₂ = 0 ∨ o₂ = 6 ∨ o₂ = 10 ∨ o₂ = 16 := by
    rcases h₂ with h | h | h <;> omega
  have ho₃ : o₃ = 0 ∨ o₃ = 6 ∨ o₃ = 10 ∨ o₃ = 16 := by
    rcases h₃ with h | h | h <;> omega
  rcases ho₀ with ho₀ | ho₀ | ho₀ | ho₀ <;>
    rcases ho₁ with ho₁ | ho₁ | ho₁ | ho₁ <;>
    rcases ho₂ with ho₂ | ho₂ | ho₂ | ho₂ <;>
    rcases ho₃ with ho₃ | ho₃ | ho₃ | ho₃ <;> omega

/-- In the `16+0+0+0` branch, the component of colored order sixteen can
contribute at most two copies of `μ=3`.  Thus a global multiplicity lower
bound of four forces the other three components to contribute at least two.

The three remaining components are kept abstract here so that a caller may
choose the order-sixteen component before reindexing its component type. -/
theorem sizeTwoScreenRecord_order_sixteen_forces_other_muThreeMultiplicity
    (o m m₁ m₂ m₃ : ℕ)
    (h : IsSizeTwoScreenRecord o m)
    (_ho : o = 16)
    (hmul : 4 ≤ m + m₁ + m₂ + m₃) :
    2 ≤ m₁ + m₂ + m₃ := by
  have hm : m ≤ 2 := sizeTwoScreenRecord_muThreeMultiplicity_le_two h
  omega

/-- In the `10+6+0+0` branch, each exceptional component contributes exactly
one copy of `μ=3`.  Hence the two remaining components must together
contribute at least two when the global multiplicity is at least four.

As above, the arguments are deliberately order-independent: callers can use
this after selecting and reindexing the order-ten and order-six components. -/
theorem two_sizeTwoScreenRecords_ten_six_force_other_muThreeMultiplicity
    (o₁ o₂ m₁ m₂ m₃ m₄ : ℕ)
    (h₁ : IsSizeTwoScreenRecord o₁ m₁)
    (h₂ : IsSizeTwoScreenRecord o₂ m₂)
    (ho₁ : o₁ = 10)
    (ho₂ : o₂ = 6)
    (hmul : 4 ≤ m₁ + m₂ + m₃ + m₄) :
    2 ≤ m₃ + m₄ := by
  have hm₁ : m₁ = 1 :=
    sizeTwoScreenRecord_order_six_or_ten_muThreeMultiplicity_eq_one h₁ (Or.inr ho₁)
  have hm₂ : m₂ = 1 :=
    sizeTwoScreenRecord_order_six_or_ten_muThreeMultiplicity_eq_one h₂ (Or.inl ho₂)
  omega

end Erdos85
