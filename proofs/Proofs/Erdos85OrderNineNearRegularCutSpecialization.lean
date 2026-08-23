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

/-- Algebraic conversion of the zero-defect-boundary cut identity to equation
(3).  This theorem isolates all Nat-subtraction side conditions: ordinary
incidences are at most nine, high-root incidences at most ten, and the shore
is proper inside the 78 ordinary vertices. -/
theorem orderNine_ordinary_square_moment_of_zero_cut
    {O : Type*} [Fintype O] [DecidableEq O]
    (f : O → ℕ) (s b₁ b₂ b₃ : ℕ)
    (hfle : ∀ x, f x ≤ 9)
    (hb₁ : b₁ ≤ 10) (hb₂ : b₂ ≤ 10) (hb₃ : b₃ ≤ 10)
    (hs : s ≤ 78)
    (hbsum : b₁ + b₂ + b₃ ≤ 9 * s)
    (hsum : (∑ x, f x) = 9 * s - (b₁ + b₂ + b₃))
    (hcut : (∑ x, f x * (9 - f x)) +
      (b₁ * (10 - b₁) + b₂ * (10 - b₂) + b₃ * (10 - b₃)) =
        s * (81 - s)) :
    (∑ x, (f x) ^ 2) +
      (b₁ * (b₁ - 1) + b₂ * (b₂ - 1) + b₃ * (b₃ - 1)) = s ^ 2 := by
  have hordCast :
      (((∑ x, f x * (9 - f x) : ℕ) : ℕ) : ℤ) =
        ∑ x, (f x : ℤ) * (9 - f x) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Nat.cast_mul, Nat.cast_sub (hfle x)]
    norm_num
  have hhighCast :
      ((b₁ * (10 - b₁) + b₂ * (10 - b₂) + b₃ * (10 - b₃) : ℕ) : ℤ) =
        (b₁ : ℤ) * (10 - b₁) + (b₂ : ℤ) * (10 - b₂) +
          (b₃ : ℤ) * (10 - b₃) := by
    push_cast [Nat.cast_sub hb₁, Nat.cast_sub hb₂, Nat.cast_sub hb₃]
    rfl
  have hrhsCast : ((s * (81 - s) : ℕ) : ℤ) =
      (s : ℤ) * (81 - s) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : s ≤ 81)]
    norm_num
  have hcutZ := congrArg (fun n : ℕ => (n : ℤ)) hcut
  push_cast at hcutZ
  simp_rw [Nat.cast_sub (hfle _)] at hcutZ
  rw [Nat.cast_sub hb₁, Nat.cast_sub hb₂, Nat.cast_sub hb₃,
    Nat.cast_sub (by omega : s ≤ 81)] at hcutZ
  norm_num at hcutZ
  have hsumZ : (∑ x, (f x : ℤ)) =
      9 * (s : ℤ) - ((b₁ : ℤ) + b₂ + b₃) := by
    exact_mod_cast hsum
  have hordAlg : (∑ x, (f x : ℤ) * (9 - f x)) =
      9 * (∑ x, (f x : ℤ)) - ∑ x, (f x : ℤ) ^ 2 := by
    simp_rw [mul_sub, mul_comm (f _ : ℤ) 9]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [pow_two]
  have hcoll : ∀ b : ℕ,
      (b : ℤ) * ((b - 1 : ℕ) : ℤ) = (b : ℤ) * ((b : ℤ) - 1) := by
    intro b
    by_cases hb : b = 0
    · simp [hb]
    · rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hb)]
      norm_num
  rw [hordAlg, hsumZ] at hcutZ
  have hgoalZ : ((∑ x, f x ^ 2 : ℕ) : ℤ) +
      ((b₁ * (b₁ - 1) + b₂ * (b₂ - 1) + b₃ * (b₃ - 1) : ℕ) : ℤ) =
        ((s ^ 2 : ℕ) : ℤ) := by
    push_cast
    rw [hcoll b₁, hcoll b₂, hcoll b₃]
    ring_nf at hcutZ ⊢
    linarith
  exact_mod_cast hgoalZ

/-- Arbitrary-boundary version of equation (3): a defect boundary of size
`δ` contributes exactly `δ` to the square moment. -/
theorem orderNine_ordinary_square_moment_of_cut
    {O : Type*} [Fintype O] [DecidableEq O]
    (f : O → ℕ) (s b₁ b₂ b₃ δ : ℕ)
    (hfle : ∀ x, f x ≤ 9)
    (hb₁ : b₁ ≤ 10) (hb₂ : b₂ ≤ 10) (hb₃ : b₃ ≤ 10)
    (hs : s ≤ 78)
    (hbsum : b₁ + b₂ + b₃ ≤ 9 * s)
    (hsum : (∑ x, f x) = 9 * s - (b₁ + b₂ + b₃))
    (hcut : δ + (∑ x, f x * (9 - f x)) +
      (b₁ * (10 - b₁) + b₂ * (10 - b₂) + b₃ * (10 - b₃)) =
        s * (81 - s)) :
    (∑ x, (f x) ^ 2) +
      (b₁ * (b₁ - 1) + b₂ * (b₂ - 1) + b₃ * (b₃ - 1)) =
        s ^ 2 + δ := by
  have hcutZ := congrArg (fun n : ℕ => (n : ℤ)) hcut
  push_cast at hcutZ
  simp_rw [Nat.cast_sub (hfle _)] at hcutZ
  rw [Nat.cast_sub hb₁, Nat.cast_sub hb₂, Nat.cast_sub hb₃,
    Nat.cast_sub (by omega : s ≤ 81)] at hcutZ
  norm_num at hcutZ
  have hsumZ : (∑ x, (f x : ℤ)) =
      9 * (s : ℤ) - ((b₁ : ℤ) + b₂ + b₃) := by
    exact_mod_cast hsum
  have hordAlg : (∑ x, (f x : ℤ) * (9 - f x)) =
      9 * (∑ x, (f x : ℤ)) - ∑ x, (f x : ℤ) ^ 2 := by
    simp_rw [mul_sub, mul_comm (f _ : ℤ) 9]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [pow_two]
  have hcoll : ∀ b : ℕ,
      (b : ℤ) * ((b - 1 : ℕ) : ℤ) = (b : ℤ) * ((b : ℤ) - 1) := by
    intro b
    by_cases hb : b = 0
    · simp [hb]
    · rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hb)]
      norm_num
  rw [hordAlg, hsumZ] at hcutZ
  have hgoalZ : ((∑ x, f x ^ 2 : ℕ) : ℤ) +
      ((b₁ * (b₁ - 1) + b₂ * (b₂ - 1) + b₃ * (b₃ - 1) : ℕ) : ℤ) =
        (((s ^ 2 + δ : ℕ) : ℤ)) := by
    push_cast
    rw [hcoll b₁, hcoll b₂, hcoll b₃]
    ring_nf at hcutZ ⊢
    linarith
  exact_mod_cast hgoalZ

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

/-- The arbitrary-boundary square-moment inequality gives the sharp bound
`CutLower ≤ δ`. -/
theorem orderNineNearRegularCutLower_le_of_ordinary_moments
    {O : Type*} [Fintype O] [DecidableEq O]
    (hcard : Fintype.card O = 78)
    (f : O → ℕ) (s b₁ b₂ b₃ δ : ℕ)
    (hsum : (∑ x, f x) = 9 * s - (b₁ + b₂ + b₃))
    (hsq : (∑ x, (f x) ^ 2) +
      (b₁ * (b₁ - 1) + b₂ * (b₂ - 1) + b₃ * (b₃ - 1)) ≤
        s ^ 2 + δ) :
    orderNineNearRegularCutLower s b₁ b₂ b₃ ≤ δ := by
  have hbal := balancedSquareSum_le_sum_sq_of_card_78 hcard f
  rw [hsum] at hbal
  let c := b₁ * (b₁ - 1) + b₂ * (b₂ - 1) + b₃ * (b₃ - 1)
  have hnat : orderNineBalancedSquareSum
        (9 * s - (b₁ + b₂ + b₃)) + c ≤ s ^ 2 + δ := by
    exact (Nat.add_le_add_right hbal c).trans hsq
  have hnatZ :
      (orderNineBalancedSquareSum (9 * s - (b₁ + b₂ + b₃)) : ℤ) +
        (c : ℤ) ≤ ((s ^ 2 + δ : ℕ) : ℤ) := by
    exact_mod_cast hnat
  unfold orderNineNearRegularCutLower
  dsimp only [c] at hnatZ
  push_cast at hnatZ ⊢
  ring_nf at hnatZ ⊢
  linarith

/-- If the sharp cut lower bound is attained, then the ordinary square
moment itself attains the balanced minimum. -/
theorem orderNine_balancedSquare_eq_of_cutLower_eq
    {O : Type*} [Fintype O] [DecidableEq O]
    (f : O → ℕ) (s b₁ b₂ b₃ δ : ℕ)
    (hsum : (∑ x, f x) = 9 * s - (b₁ + b₂ + b₃))
    (hsq : (∑ x, (f x) ^ 2) +
      (b₁ * (b₁ - 1) + b₂ * (b₂ - 1) + b₃ * (b₃ - 1)) =
        s ^ 2 + δ)
    (hsharp : orderNineNearRegularCutLower s b₁ b₂ b₃ = δ) :
    orderNineBalancedSquareSum (∑ x, f x) = ∑ x, (f x) ^ 2 := by
  let c := b₁ * (b₁ - 1) + b₂ * (b₂ - 1) + b₃ * (b₃ - 1)
  have hsharpZ := hsharp
  unfold orderNineNearRegularCutLower at hsharpZ
  have hbalZ :
      (orderNineBalancedSquareSum (9 * s - (b₁ + b₂ + b₃)) : ℤ) +
          (c : ℤ) = ((s ^ 2 + δ : ℕ) : ℤ) := by
    dsimp only [c]
    push_cast at hsharpZ ⊢
    linarith
  have hbal :
      orderNineBalancedSquareSum (9 * s - (b₁ + b₂ + b₃)) + c =
        s ^ 2 + δ := by
    exact_mod_cast hbalZ
  rw [← hsum] at hbal
  dsimp only [c] at hbal
  omega

/-- Complete equality consumer: a sharp cut and its exact ordinary moments
produce both the two adjacent pointwise values and the exact size of the
upper-value set. -/
theorem orderNine_ordinary_partition_of_cutLower_eq
    {O : Type*} [Fintype O] [DecidableEq O]
    (hcard : Fintype.card O = 78)
    (f : O → ℕ) (s b₁ b₂ b₃ δ : ℕ)
    (hsum : (∑ x, f x) = 9 * s - (b₁ + b₂ + b₃))
    (hsq : (∑ x, (f x) ^ 2) +
      (b₁ * (b₁ - 1) + b₂ * (b₂ - 1) + b₃ * (b₃ - 1)) =
        s ^ 2 + δ)
    (hsharp : orderNineNearRegularCutLower s b₁ b₂ b₃ = δ) :
    (∀ x, f x = (∑ y, f y) / 78 ∨ f x = (∑ y, f y) / 78 + 1) ∧
    (Finset.univ.filter fun x =>
      f x = (∑ y, f y) / 78 + 1).card = (∑ y, f y) % 78 := by
  have heq := orderNine_balancedSquare_eq_of_cutLower_eq
    f s b₁ b₂ b₃ δ hsum hsq hsharp
  exact ⟨balancedSquare_eq_iff_pointwise_of_card_78 hcard f heq,
    balancedSquare_eq_upper_card_of_card_78 hcard f heq⟩

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
#print axioms orderNine_ordinary_square_moment_of_zero_cut
#print axioms orderNine_ordinary_square_moment_of_cut
#print axioms orderNineNearRegularCutLower_le_of_ordinary_moments
#print axioms orderNine_balancedSquare_eq_of_cutLower_eq
#print axioms orderNine_ordinary_partition_of_cutLower_eq

end Erdos85
