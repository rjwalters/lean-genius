import Proofs.Erdos85OrderNineBalancedSquareBound

/-! # From ordinary degree moments to q=9 cut admissibility

This is the arithmetic specialization between the exact graph cut identity
and the finite component-order classifier.  Once the three high vertices are
split off, equation (3) says that the ordinary square moment plus the three
high-root collision terms is at most `s²` for a zero-boundary shore.  The
sharp 78-entry balanced-square theorem then gives exactly
`orderNineNearRegularCutLower ≤ 0`.
-/

open Finset

namespace Erdos85

/-- A 78-entry ordinary degree vector with the q=9 incidence total and the
zero-boundary square-moment inequality implies the classifier's cut lower
bound. -/
theorem orderNineNearRegularCutLower_nonpos_of_ordinary_moments
    {O : Type*} [Fintype O] [DecidableEq O]
    (hcard : Fintype.card O = 78)
    (f : O → ℕ) (s b₁ b₂ b₃ : ℕ)
    (hsum : (∑ x, f x) = 9 * s - (b₁ + b₂ + b₃))
    (hsq : (∑ x, (f x) ^ 2) +
      (b₁ * (b₁ - 1) + b₂ * (b₂ - 1) + b₃ * (b₃ - 1)) ≤ s ^ 2) :
    orderNineNearRegularCutLower s b₁ b₂ b₃ ≤ 0 := by
  have hbal := balancedSquareSum_le_sum_sq_of_card_78 hcard f
  rw [hsum] at hbal
  let c := b₁ * (b₁ - 1) + b₂ * (b₂ - 1) + b₃ * (b₃ - 1)
  have hnat : orderNineBalancedSquareSum
        (9 * s - (b₁ + b₂ + b₃)) + c ≤ s ^ 2 := by
    exact (Nat.add_le_add_right hbal c).trans hsq
  have hnatZ :
      (orderNineBalancedSquareSum (9 * s - (b₁ + b₂ + b₃)) : ℤ) +
        (c : ℤ) ≤ (s ^ 2 : ℕ) := by
    exact_mod_cast hnat
  unfold orderNineNearRegularCutLower
  dsimp only [c] at hnatZ
  rw [Nat.cast_pow] at hnatZ
  ring_nf at hnatZ ⊢
  linarith

/-- Two-sided form matching `orderNineNearRegularComponentAdmissible`.
The second ordinary vector is the complement shore's incidence vector. -/
theorem orderNineNearRegularComponentAdmissible_of_ordinary_moments
    {O : Type*} [Fintype O] [DecidableEq O]
    (hcard : Fintype.card O = 78)
    (f g : O → ℕ) (s b₁ b₂ b₃ : ℕ)
    (hfsum : (∑ x, f x) = 9 * s - (b₁ + b₂ + b₃))
    (hfsq : (∑ x, (f x) ^ 2) +
      (b₁ * (b₁ - 1) + b₂ * (b₂ - 1) + b₃ * (b₃ - 1)) ≤ s ^ 2)
    (hgsum : (∑ x, g x) =
      9 * (78 - s) - ((10 - b₁) + (10 - b₂) + (10 - b₃)))
    (hgsq : (∑ x, (g x) ^ 2) +
      ((10 - b₁) * (10 - b₁ - 1) +
       (10 - b₂) * (10 - b₂ - 1) +
       (10 - b₃) * (10 - b₃ - 1)) ≤ (78 - s) ^ 2) :
    orderNineNearRegularComponentAdmissible s b₁ b₂ b₃ := by
  constructor
  · exact orderNineNearRegularCutLower_nonpos_of_ordinary_moments
      hcard f s b₁ b₂ b₃ hfsum hfsq
  · exact orderNineNearRegularCutLower_nonpos_of_ordinary_moments
      hcard g (78 - s) (10 - b₁) (10 - b₂) (10 - b₃) hgsum hgsq

#print axioms orderNineNearRegularCutLower_nonpos_of_ordinary_moments
#print axioms orderNineNearRegularComponentAdmissible_of_ordinary_moments

end Erdos85
