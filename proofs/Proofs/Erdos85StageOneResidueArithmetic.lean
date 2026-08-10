import Mathlib

/-!
# Finite residue arithmetic for the zero-layer Stage-1 exact cover

The eight pair-profile differences are distinct residues modulo twelve and
none is divisible by three.  After sorting their natural representatives,
this elementary terminal identifies the list exactly.  It is the finite
arithmetic input to the rational three-color action of the service graph.
-/

namespace Erdos85

/-- Eight increasing residues below twelve, all nonzero modulo three, are
the full set of non-three-divisible residues. -/
theorem eight_sorted_nonzero_mod_three_residues
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ℕ)
    (h01 : a₀ < a₁) (h12 : a₁ < a₂) (h23 : a₂ < a₃)
    (h34 : a₃ < a₄) (h45 : a₄ < a₅) (h56 : a₅ < a₆)
    (h67 : a₆ < a₇) (hmax : a₇ < 12)
    (hm₀ : a₀ % 3 ≠ 0) (hm₁ : a₁ % 3 ≠ 0)
    (hm₂ : a₂ % 3 ≠ 0) (hm₃ : a₃ % 3 ≠ 0)
    (hm₄ : a₄ % 3 ≠ 0) (hm₅ : a₅ % 3 ≠ 0)
    (hm₆ : a₆ % 3 ≠ 0) (hm₇ : a₇ % 3 ≠ 0) :
    a₀ = 1 ∧ a₁ = 2 ∧ a₂ = 4 ∧ a₃ = 5 ∧
      a₄ = 7 ∧ a₅ = 8 ∧ a₆ = 10 ∧ a₇ = 11 := by
  omega

/-- Consequently the exact cover contains four residues in each nonzero
class modulo three. -/
theorem eight_sorted_nonzero_mod_three_class_counts
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ℕ)
    (h01 : a₀ < a₁) (h12 : a₁ < a₂) (h23 : a₂ < a₃)
    (h34 : a₃ < a₄) (h45 : a₄ < a₅) (h56 : a₅ < a₆)
    (h67 : a₆ < a₇) (hmax : a₇ < 12)
    (hm₀ : a₀ % 3 ≠ 0) (hm₁ : a₁ % 3 ≠ 0)
    (hm₂ : a₂ % 3 ≠ 0) (hm₃ : a₃ % 3 ≠ 0)
    (hm₄ : a₄ % 3 ≠ 0) (hm₅ : a₅ % 3 ≠ 0)
    (hm₆ : a₆ % 3 ≠ 0) (hm₇ : a₇ % 3 ≠ 0) :
    ({i ∈ Finset.range 8 |
      [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇][i]! % 3 = 1}).card = 4 ∧
    ({i ∈ Finset.range 8 |
      [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇][i]! % 3 = 2}).card = 4 := by
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
    eight_sorted_nonzero_mod_three_residues
      a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ h01 h12 h23 h34 h45 h56 h67 hmax
        hm₀ hm₁ hm₂ hm₃ hm₄ hm₅ hm₆ hm₇
  decide

/-- Three pairwise-distinct residues modulo three exhaust the three residue
classes.  This is the row-offset arithmetic used to show that the three
missing colors in the omitting case are distinct. -/
theorem three_pairwise_distinct_mod_three_cases (a b c : ℕ)
    (hab : a % 3 ≠ b % 3) (hac : a % 3 ≠ c % 3)
    (hbc : b % 3 ≠ c % 3) :
    (a % 3 = 0 ∧ b % 3 = 1 ∧ c % 3 = 2) ∨
    (a % 3 = 0 ∧ b % 3 = 2 ∧ c % 3 = 1) ∨
    (a % 3 = 1 ∧ b % 3 = 0 ∧ c % 3 = 2) ∨
    (a % 3 = 1 ∧ b % 3 = 2 ∧ c % 3 = 0) ∨
    (a % 3 = 2 ∧ b % 3 = 0 ∧ c % 3 = 1) ∨
    (a % 3 = 2 ∧ b % 3 = 1 ∧ c % 3 = 0) := by
  omega

end Erdos85
