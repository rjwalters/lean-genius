import Proofs.Erdos85ThreeSeparatorUniformWingIntervals

/-!
# Bottom-slice wing rigidity

At the lower endpoint allowed by B45, the three exceptional bits and the
three wing slacks satisfy a tiny exact ledger.  For `q = 3r+2` it forces
all bits to be one and all slacks to vanish.  For `q = 3r+1` it forces
either two bits and zero slack, or three bits and one unit of total slack;
both cases give the same unordered wing profile.  These are B48a/B48b.
-/

namespace Erdos85

/-- Boolean/slack core of B48a, written without truncated subtraction. -/
theorem bottomWing_threeTwo_bits_and_slacks_rigid
    (e₁ e₂ e₃ s₁ s₂ s₃ : ℕ)
    (he₁ : e₁ ≤ 1) (he₂ : e₂ ≤ 1) (he₃ : e₃ ≤ 1)
    (hledger : s₁ + s₂ + s₃ + 3 = e₁ + e₂ + e₃) :
    e₁ = 1 ∧ e₂ = 1 ∧ e₃ = 1 ∧
      s₁ = 0 ∧ s₂ = 0 ∧ s₃ = 0 := by
  omega

/-- Boolean/slack core of B48b. -/
theorem bottomWing_threeOne_bits_and_slacks_cases
    (e₁ e₂ e₃ s₁ s₂ s₃ : ℕ)
    (he₁ : e₁ ≤ 1) (he₂ : e₂ ≤ 1) (he₃ : e₃ ≤ 1)
    (hledger : s₁ + s₂ + s₃ + 2 = e₁ + e₂ + e₃) :
    ((e₁ + e₂ + e₃ = 2) ∧ s₁ = 0 ∧ s₂ = 0 ∧ s₃ = 0) ∨
      (e₁ = 1 ∧ e₂ = 1 ∧ e₃ = 1 ∧ s₁ + s₂ + s₃ = 1) := by
  omega

/-- Exact B48a wing sizes.  The equations `mᵢ+eᵢ+1=b+sᵢ` are the
subtraction-free form of `sᵢ=mᵢ-(b-1-eᵢ)`. -/
theorem bottomWing_threeTwo_exact_profile
    (b e₁ e₂ e₃ s₁ s₂ s₃ m₁ m₂ m₃ : ℕ)
    (hb : 2 ≤ b)
    (he₁ : e₁ ≤ 1) (he₂ : e₂ ≤ 1) (he₃ : e₃ ≤ 1)
    (hledger : s₁ + s₂ + s₃ + 3 = e₁ + e₂ + e₃)
    (hm₁ : m₁ + e₁ + 1 = b + s₁)
    (hm₂ : m₂ + e₂ + 1 = b + s₂)
    (hm₃ : m₃ + e₃ + 1 = b + s₃) :
    m₁ = b - 2 ∧ m₂ = b - 2 ∧ m₃ = b - 2 := by
  have hrigid := bottomWing_threeTwo_bits_and_slacks_rigid
    e₁ e₂ e₃ s₁ s₂ s₃ he₁ he₂ he₃ hledger
  omega

/-- Exact unordered B48b profile, expanded into its three possible
positions for the unique `b-1` wing. -/
theorem bottomWing_threeOne_exact_profile
    (b e₁ e₂ e₃ s₁ s₂ s₃ m₁ m₂ m₃ : ℕ)
    (hb : 2 ≤ b)
    (he₁ : e₁ ≤ 1) (he₂ : e₂ ≤ 1) (he₃ : e₃ ≤ 1)
    (hledger : s₁ + s₂ + s₃ + 2 = e₁ + e₂ + e₃)
    (hm₁ : m₁ + e₁ + 1 = b + s₁)
    (hm₂ : m₂ + e₂ + 1 = b + s₂)
    (hm₃ : m₃ + e₃ + 1 = b + s₃) :
    (m₁ = b - 1 ∧ m₂ = b - 2 ∧ m₃ = b - 2) ∨
      (m₁ = b - 2 ∧ m₂ = b - 1 ∧ m₃ = b - 2) ∨
      (m₁ = b - 2 ∧ m₂ = b - 2 ∧ m₃ = b - 1) := by
  have hcases := bottomWing_threeOne_bits_and_slacks_cases
    e₁ e₂ e₃ s₁ s₂ s₃ he₁ he₂ he₃ hledger
  omega

end Erdos85

#print axioms Erdos85.bottomWing_threeTwo_bits_and_slacks_rigid
#print axioms Erdos85.bottomWing_threeOne_bits_and_slacks_cases
#print axioms Erdos85.bottomWing_threeTwo_exact_profile
#print axioms Erdos85.bottomWing_threeOne_exact_profile
