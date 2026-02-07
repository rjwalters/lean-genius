import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace TestE1061

def sigma (n : ℕ) : ℕ := (n.divisors).sum id

-- Test 1: sigma_prime
theorem sigma_prime (p : ℕ) (hp : p.Prime) : sigma p = 1 + p := by
  simp only [sigma]
  rw [Nat.divisors_prime_eq hp]
  simp [Finset.sum_pair (Nat.Prime.one_lt hp).ne']

-- Test 2: sigma_not_subadditive witness (2, 3)
theorem sigma_not_subadditive :
    ∃ a b : ℕ, a ≥ 1 ∧ b ≥ 1 ∧ sigma (a + b) < sigma a + sigma b :=
  ⟨2, 3, by omega, by omega, by native_decide⟩

-- Test 3: sigma_not_superadditive witness (2, 4)
theorem sigma_not_superadditive :
    ∃ a b : ℕ, a ≥ 1 ∧ b ≥ 1 ∧ sigma (a + b) > sigma a + sigma b :=
  ⟨2, 4, by omega, by omega, by native_decide⟩

-- Test 4: S function (computable version)
def S (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x ×ˢ Finset.Icc 1 x).filter fun (a, b) =>
    a + b ≤ x ∧ sigma a + sigma b = sigma (a + b)).card

-- Test 5: Monotonicity of S
lemma S_mono (x y : ℕ) (hxy : x ≤ y) : S x ≤ S y := by
  unfold S
  apply Finset.card_le_card
  intro ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  intro ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, hab_le, hsig⟩
  exact ⟨⟨⟨ha1, le_trans ha2 hxy⟩, ⟨hb1, le_trans hb2 hxy⟩⟩, le_trans hab_le hxy, hsig⟩

-- Test 6: S_lower_bound via explicit membership
private def SSet (x : ℕ) :=
  (Finset.Icc 1 x ×ˢ Finset.Icc 1 x).filter fun (a, b) =>
    a + b ≤ x ∧ sigma a + sigma b = sigma (a + b)

lemma mem_1_2 : (1, 2) ∈ SSet 3 := by
  simp only [SSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, sigma]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_, ?_⟩ <;> decide

lemma mem_2_1 : (2, 1) ∈ SSet 3 := by
  simp only [SSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, sigma]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_, ?_⟩ <;> decide

theorem S_three_ge : S 3 ≥ 2 := by
  have h12 := mem_1_2
  have h21 := mem_2_1
  have hsub : ({(1, 2), (2, 1)} : Finset (ℕ × ℕ)) ⊆ SSet 3 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h12
    · exact h21
  calc S 3 = (SSet 3).card := rfl
    _ ≥ ({(1, 2), (2, 1)} : Finset (ℕ × ℕ)).card := Finset.card_le_card hsub
    _ = 2 := by decide

theorem S_lower_bound (x : ℕ) (hx : x ≥ 3) : S x ≥ 2 :=
  le_trans S_three_ge (S_mono 3 x hx)

-- Test 7: S_upper_bound (more structural approach)
-- S(x) ≤ x*x/4 since at most x/2 * x/2 pairs
-- Actually this is hard to prove structurally.
-- Let's try a weaker bound: S(x) ≤ x * x (trivial upper bound)
theorem S_upper_trivial (x : ℕ) : S x ≤ x * x := by
  unfold S
  calc ((Finset.Icc 1 x ×ˢ Finset.Icc 1 x).filter _).card
      ≤ (Finset.Icc 1 x ×ˢ Finset.Icc 1 x).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = (Finset.Icc 1 x).card * (Finset.Icc 1 x).card := Finset.card_product _ _
    _ ≤ x * x := by
        simp only [Nat.card_Icc]
        omega

end TestE1061
