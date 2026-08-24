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

private theorem complementaryWing_eq_add_two
    (q a b m n : ℕ) (hb : 2 ≤ b)
    (hab : a + b = q - 1) (hm : m = b - 2)
    (hwing : m + n = q - 1) : n = a + 2 := by
  omega

private theorem complementaryWing_eq_add_one
    (q a b m n : ℕ) (hb : 1 ≤ b)
    (hab : a + b = q - 1) (hm : m = b - 1)
    (hwing : m + n = q - 1) : n = a + 1 := by
  omega

/-- Full B48a paired wing profile, including the complementary R-wing
sizes `nᵢ`. -/
theorem bottomWing_threeTwo_exact_paired_profile
    (q a b e₁ e₂ e₃ s₁ s₂ s₃ m₁ m₂ m₃ n₁ n₂ n₃ : ℕ)
    (hb : 2 ≤ b)
    (hab : a + b = q - 1)
    (he₁ : e₁ ≤ 1) (he₂ : e₂ ≤ 1) (he₃ : e₃ ≤ 1)
    (hledger : s₁ + s₂ + s₃ + 3 = e₁ + e₂ + e₃)
    (hm₁ : m₁ + e₁ + 1 = b + s₁)
    (hm₂ : m₂ + e₂ + 1 = b + s₂)
    (hm₃ : m₃ + e₃ + 1 = b + s₃)
    (hwing₁ : m₁ + n₁ = q - 1)
    (hwing₂ : m₂ + n₂ = q - 1)
    (hwing₃ : m₃ + n₃ = q - 1) :
    (m₁ = b - 2 ∧ n₁ = a + 2) ∧
      (m₂ = b - 2 ∧ n₂ = a + 2) ∧
      (m₃ = b - 2 ∧ n₃ = a + 2) := by
  have hm := bottomWing_threeTwo_exact_profile
    b e₁ e₂ e₃ s₁ s₂ s₃ m₁ m₂ m₃ hb he₁ he₂ he₃
      hledger hm₁ hm₂ hm₃
  rcases hm with ⟨hm₁', hm₂', hm₃'⟩
  exact ⟨⟨hm₁', complementaryWing_eq_add_two q a b m₁ n₁ hb hab hm₁' hwing₁⟩,
    ⟨hm₂', complementaryWing_eq_add_two q a b m₂ n₂ hb hab hm₂' hwing₂⟩,
    ⟨hm₃', complementaryWing_eq_add_two q a b m₃ n₃ hb hab hm₃' hwing₃⟩⟩

/-- Full B48b paired profile.  The unique larger K-wing is paired with
the unique smaller R-wing. -/
theorem bottomWing_threeOne_exact_paired_profile
    (q a b e₁ e₂ e₃ s₁ s₂ s₃ m₁ m₂ m₃ n₁ n₂ n₃ : ℕ)
    (hb : 2 ≤ b)
    (hab : a + b = q - 1)
    (he₁ : e₁ ≤ 1) (he₂ : e₂ ≤ 1) (he₃ : e₃ ≤ 1)
    (hledger : s₁ + s₂ + s₃ + 2 = e₁ + e₂ + e₃)
    (hm₁ : m₁ + e₁ + 1 = b + s₁)
    (hm₂ : m₂ + e₂ + 1 = b + s₂)
    (hm₃ : m₃ + e₃ + 1 = b + s₃)
    (hwing₁ : m₁ + n₁ = q - 1)
    (hwing₂ : m₂ + n₂ = q - 1)
    (hwing₃ : m₃ + n₃ = q - 1) :
    ((m₁ = b - 1 ∧ n₁ = a + 1) ∧
      (m₂ = b - 2 ∧ n₂ = a + 2) ∧
      (m₃ = b - 2 ∧ n₃ = a + 2)) ∨
    ((m₁ = b - 2 ∧ n₁ = a + 2) ∧
      (m₂ = b - 1 ∧ n₂ = a + 1) ∧
      (m₃ = b - 2 ∧ n₃ = a + 2)) ∨
    ((m₁ = b - 2 ∧ n₁ = a + 2) ∧
      (m₂ = b - 2 ∧ n₂ = a + 2) ∧
      (m₃ = b - 1 ∧ n₃ = a + 1)) := by
  have hm := bottomWing_threeOne_exact_profile
    b e₁ e₂ e₃ s₁ s₂ s₃ m₁ m₂ m₃ hb he₁ he₂ he₃
      hledger hm₁ hm₂ hm₃
  rcases hm with hm | hm | hm
  · rcases hm with ⟨hm₁', hm₂', hm₃'⟩
    left
    exact ⟨⟨hm₁', complementaryWing_eq_add_one q a b m₁ n₁
          (by omega) hab hm₁' hwing₁⟩,
      ⟨hm₂', complementaryWing_eq_add_two q a b m₂ n₂ hb hab hm₂' hwing₂⟩,
      ⟨hm₃', complementaryWing_eq_add_two q a b m₃ n₃ hb hab hm₃' hwing₃⟩⟩
  · rcases hm with ⟨hm₁', hm₂', hm₃'⟩
    right; left
    exact ⟨⟨hm₁', complementaryWing_eq_add_two q a b m₁ n₁ hb hab hm₁' hwing₁⟩,
      ⟨hm₂', complementaryWing_eq_add_one q a b m₂ n₂
          (by omega) hab hm₂' hwing₂⟩,
      ⟨hm₃', complementaryWing_eq_add_two q a b m₃ n₃ hb hab hm₃' hwing₃⟩⟩
  · rcases hm with ⟨hm₁', hm₂', hm₃'⟩
    right; right
    exact ⟨⟨hm₁', complementaryWing_eq_add_two q a b m₁ n₁ hb hab hm₁' hwing₁⟩,
      ⟨hm₂', complementaryWing_eq_add_two q a b m₂ n₂ hb hab hm₂' hwing₂⟩,
      ⟨hm₃', complementaryWing_eq_add_one q a b m₃ n₃
          (by omega) hab hm₃' hwing₃⟩⟩

end Erdos85

#print axioms Erdos85.bottomWing_threeTwo_bits_and_slacks_rigid
#print axioms Erdos85.bottomWing_threeOne_bits_and_slacks_cases
#print axioms Erdos85.bottomWing_threeTwo_exact_profile
#print axioms Erdos85.bottomWing_threeOne_exact_profile
#print axioms Erdos85.bottomWing_threeTwo_exact_paired_profile
#print axioms Erdos85.bottomWing_threeOne_exact_paired_profile
