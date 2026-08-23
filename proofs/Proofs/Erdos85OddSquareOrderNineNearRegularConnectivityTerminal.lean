import Proofs.Erdos85OddSquareOrderNineNearRegularCutArithmetic

/-! # Component-balance terminal for the q=9 ordinary defect graph

This module joins the two arithmetic halves of the reviewed connectivity
argument.  A component not containing the unique bin-three point has `n₀`
bin-zero and `n₁` bin-one vertices.  Counting its B0--B1 defect edges in the
two directions gives `3 n₀ = 5 n₁`, hence its order is divisible by eight.
The near-regular cut classification excludes every such proper order.
-/

namespace Erdos85

/-- The exact `3 n₀ = 5 n₁` component balance forces the total component
order to be divisible by eight. -/
theorem eight_dvd_of_three_mul_eq_five_mul
    (n₀ n₁ : ℕ) (hbalance : 3 * n₀ = 5 * n₁) :
    8 ∣ n₀ + n₁ := by
  have hfive : 5 ∣ n₀ := by
    omega
  obtain ⟨k, rfl⟩ := hfive
  have hn₁ : n₁ = 3 * k := by
    omega
  subst n₁
  use k
  omega

/-- Abstract terminal consumed by the graph-level connectivity proof.

The graph layer only has to provide a nonempty proper component, its three
high-root incidence counts, the two cut inequalities, parity, and the
two-sided B0--B1 edge count.  No component enumeration or graph census is
hidden in this statement. -/
theorem false_of_orderNine_nearRegular_proper_component_balance
    (s : Fin 78) (b₁ b₂ b₃ : Fin 11) (n₀ n₁ : ℕ)
    (hs : s.1 ≠ 0)
    (hcard : s.1 = n₀ + n₁)
    (hparity : (b₁.1 + b₂.1 + b₃.1) % 2 = 0)
    (hadm : orderNineNearRegularComponentAdmissible s.1 b₁.1 b₂.1 b₃.1)
    (hbalance : 3 * n₀ = 5 * n₁) :
    False := by
  have height : 8 ∣ s.1 := by
    rw [hcard]
    exact eight_dvd_of_three_mul_eq_five_mul n₀ n₁ hbalance
  exact orderNine_nearRegular_eight_not_dvd_proper_component_order
    s b₁ b₂ b₃ hs hparity hadm height

#print axioms eight_dvd_of_three_mul_eq_five_mul
#print axioms false_of_orderNine_nearRegular_proper_component_balance

end Erdos85
