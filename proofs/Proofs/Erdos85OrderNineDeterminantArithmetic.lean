import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Erdos85

/-- Possible first-component determinants in the order-nine character reduction. -/
def orderNineFirstFactors : Finset ℕ := {270, 297, 423, 432, 450, 459, 666, 693}

/-- Possible second-component determinants. -/
def orderNineSecondFactors : Finset ℕ := {48, 99}

/-- Possible third-component determinants. -/
def orderNineThirdFactors : Finset ℕ := {1911, 2751, 2940, 3960, 4221, 5700, 6060, 8700}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem orderNine_sqrt_certificate :
    ∀ f ∈ orderNineFirstFactors, ∀ s ∈ orderNineSecondFactors,
      ∀ t ∈ orderNineThirdFactors,
        Nat.sqrt (f * s * t) * Nat.sqrt (f * s * t) ≠ f * s * t := by
  decide +kernel

/-- The finite determinant-factor certificate: none of the128 products is a
natural square. This does not formalize the graph-to-character reduction. -/
theorem orderNine_factor_product_ne_square
    {f s t : ℕ} (hf : f ∈ orderNineFirstFactors)
    (hs : s ∈ orderNineSecondFactors) (ht : t ∈ orderNineThirdFactors)
    (n : ℕ) : f * s * t ≠ n * n := by
  intro h
  have hn := orderNine_sqrt_certificate f hf s hs t ht
  rw [h, Nat.sqrt_eq] at hn
  exact hn rfl

end Erdos85
