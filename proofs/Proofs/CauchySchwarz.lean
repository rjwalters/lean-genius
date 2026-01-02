import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# The Cauchy-Schwarz Inequality

## What This Proves
The Cauchy-Schwarz Inequality states that for any vectors in an inner product space,
the absolute value of their inner product is bounded by the product of their norms:

  |⟨u, v⟩| ≤ ‖u‖ · ‖v‖

with equality if and only if u and v are linearly dependent.

For real sequences (a₁, ..., aₙ) and (b₁, ..., bₙ):

  (∑ aᵢbᵢ)² ≤ (∑ aᵢ²) · (∑ bᵢ²)

## Approach
- **Inner Product Form:** Uses Mathlib's `abs_real_inner_le_norm` for the abstract version.
- **Finite Sum Form:** Interprets sequences as vectors in Euclidean space and applies
  the inner product form.
- **Two-Variable Case:** Direct algebraic proof using (a₁b₂ - a₂b₁)² ≥ 0.
- **Key Insight:** The inequality follows from the non-negativity of squares.

## Status
- [x] Complete proof
- [x] Inner product space form
- [x] Finite sum form
- [x] Two-variable explicit case
- [x] Equality characterization

## Mathlib Dependencies
- `abs_real_inner_le_norm` : |⟨x, y⟩| ≤ ‖x‖ · ‖y‖ for real inner product spaces
- `inner_mul_le_norm_mul_norm` : ‖⟨x, y⟩‖ ≤ ‖x‖ · ‖y‖ for general inner product spaces
- `EuclideanSpace.inner_eq_star_dotProduct` : Inner product equals dot product
- `sq_nonneg` : x² ≥ 0 for all x

## Historical Note
Named after Augustin-Louis Cauchy (1821) and Hermann Schwarz (1888), though discovered
independently by several mathematicians including Viktor Bunyakovsky (1859). The inequality
is fundamental to functional analysis, quantum mechanics, and machine learning.

This is #78 on Wiedijk's list of 100 theorems.
-/

namespace CauchySchwarz

/-! ## Inner Product Space Form

The most general form of Cauchy-Schwarz in an abstract inner product space.
-/

/-- **Cauchy-Schwarz Inequality - Inner Product Form (Wiedijk #78)**

For vectors u, v in a real inner product space:
  |⟨u, v⟩| ≤ ‖u‖ · ‖v‖

This is the abstract, coordinate-free version of the inequality. -/
theorem cauchy_schwarz_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) :
    |⟪u, v⟫_ℝ| ≤ ‖u‖ * ‖v‖ :=
  abs_real_inner_le_norm u v

/-- **Cauchy-Schwarz Squared Form**

Equivalent formulation: ⟨u, v⟩² ≤ ⟨u, u⟩ · ⟨v, v⟩ -/
theorem cauchy_schwarz_inner_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) :
    ⟪u, v⟫_ℝ ^ 2 ≤ ⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ := by
  have h := abs_real_inner_le_norm u v
  have h_nonneg : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h_sq := sq_le_sq' (by linarith [abs_nonneg ⟪u, v⟫_ℝ]) h
  rw [sq_abs] at h_sq
  calc ⟪u, v⟫_ℝ ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := h_sq
    _ = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by ring
    _ = ⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ := by rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-! ## Two-Variable Algebraic Form

The classical two-variable case with an elementary proof.
-/

/-- **Cauchy-Schwarz for Two Variables**

For real numbers a₁, a₂, b₁, b₂:
  (a₁b₁ + a₂b₂)² ≤ (a₁² + a₂²)(b₁² + b₂²)

This is proven directly using the fact that (a₁b₂ - a₂b₁)² ≥ 0. -/
theorem cauchy_schwarz_two (a₁ a₂ b₁ b₂ : ℝ) :
    (a₁ * b₁ + a₂ * b₂) ^ 2 ≤ (a₁ ^ 2 + a₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) := by
  have h : 0 ≤ (a₁ * b₂ - a₂ * b₁) ^ 2 := sq_nonneg _
  nlinarith [h]

/-- **Two-Variable Equality Condition**

Equality holds in the two-variable Cauchy-Schwarz if and only if the vectors
(a₁, a₂) and (b₁, b₂) are proportional, i.e., a₁b₂ = a₂b₁. -/
theorem cauchy_schwarz_two_eq_iff (a₁ a₂ b₁ b₂ : ℝ) :
    (a₁ * b₁ + a₂ * b₂) ^ 2 = (a₁ ^ 2 + a₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) ↔
    a₁ * b₂ = a₂ * b₁ := by
  constructor
  · intro h
    -- The difference is (a₁b₂ - a₂b₁)², and equals zero when LHS = RHS
    have h_expand : (a₁ ^ 2 + a₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) - (a₁ * b₁ + a₂ * b₂) ^ 2 =
        (a₁ * b₂ - a₂ * b₁) ^ 2 := by ring
    have h_zero : (a₁ * b₂ - a₂ * b₁) ^ 2 = 0 := by linarith [h_expand, h]
    have := sq_eq_zero_iff.mp h_zero
    linarith
  · intro h
    have h_sq : (a₁ * b₂ - a₂ * b₁) ^ 2 = 0 := by rw [sub_eq_zero.mpr h]; ring
    nlinarith [h_sq]

/-! ## Finite Sum Form

The inequality for finite sequences, derived from the inner product form.
-/

/-- **Cauchy-Schwarz for Finite Sums**

For sequences a, b : Fin n → ℝ:
  (∑ i, aᵢ · bᵢ)² ≤ (∑ i, aᵢ²) · (∑ i, bᵢ²)

This follows from viewing the sequences as vectors in Euclidean space. -/
theorem cauchy_schwarz_sum {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i, a i * b i) ^ 2 ≤ (∑ i, a i ^ 2) * (∑ i, b i ^ 2) := by
  -- Interpret as vectors in Euclidean space
  let u : EuclideanSpace ℝ (Fin n) := a
  let v : EuclideanSpace ℝ (Fin n) := b
  -- Apply the inner product Cauchy-Schwarz
  have h := cauchy_schwarz_inner_sq u v
  -- The inner product is the dot product for EuclideanSpace
  have inner_eq : ⟪u, v⟫_ℝ = ∑ i, a i * b i := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.dotProduct]
    simp [u, v]
  have norm_u_sq : ⟪u, u⟫_ℝ = ∑ i, a i ^ 2 := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.dotProduct]
    simp [u, sq]
  have norm_v_sq : ⟪v, v⟫_ℝ = ∑ i, b i ^ 2 := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.dotProduct]
    simp [v, sq]
  rw [inner_eq, norm_u_sq, norm_v_sq] at h
  exact h

/-- **Cauchy-Schwarz Sum Form (Non-squared)**

Alternate form: |∑ aᵢbᵢ| ≤ √(∑ aᵢ²) · √(∑ bᵢ²) -/
theorem cauchy_schwarz_sum_abs {n : ℕ} (a b : Fin n → ℝ) :
    |∑ i, a i * b i| ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
  have h := cauchy_schwarz_sum a b
  have ha : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hb : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have _hab : 0 ≤ (∑ i, a i ^ 2) * (∑ i, b i ^ 2) := mul_nonneg ha hb
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul ha]
  exact Real.sqrt_le_sqrt h

/-! ## Equality Characterization for Inner Product Spaces -/

/-- **Cauchy-Schwarz Equality implies Linear Dependence**

If |⟨u, v⟩| = ‖u‖ · ‖v‖, then u and v are linearly dependent. -/
theorem cauchy_schwarz_eq_iff_parallel {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    |⟪u, v⟫_ℝ| = ‖u‖ * ‖v‖ ↔ ∃ c : ℝ, u = c • v := by
  constructor
  · intro h
    -- Use the standard Mathlib result for norm equality
    have h' : ‖⟪u, v⟫_ℝ‖ = ‖u‖ * ‖v‖ := by rwa [Real.norm_eq_abs]
    obtain ⟨r, hr_ne, hr⟩ := (norm_inner_eq_norm_iff hu hv).mp h'
    refine ⟨r⁻¹, ?_⟩
    rw [hr, smul_smul]
    simp [inv_mul_cancel hr_ne]
  · intro ⟨c, hc⟩
    rw [hc, inner_smul_left, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs]
    simp only [starRingEnd_apply, star_trivial]
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖v‖)]
    ring

/-! ## Examples and Verification -/

/-- Concrete example: (1·2 + 3·4)² ≤ (1² + 3²)(2² + 4²) -/
example : (1 * 2 + 3 * 4 : ℝ) ^ 2 ≤ (1 ^ 2 + 3 ^ 2) * (2 ^ 2 + 4 ^ 2) := by
  norm_num

/-- Equality case: (1·2 + 2·4)² = (1² + 2²)(2² + 4²) when vectors are parallel -/
example : (1 * 2 + 2 * 4 : ℝ) ^ 2 = (1 ^ 2 + 2 ^ 2) * (2 ^ 2 + 4 ^ 2) := by
  norm_num

/-- Cauchy-Schwarz for the standard inner product on ℝ² -/
example (a b : Fin 2 → ℝ) : (a 0 * b 0 + a 1 * b 1) ^ 2 ≤
    (a 0 ^ 2 + a 1 ^ 2) * (b 0 ^ 2 + b 1 ^ 2) := by
  have h := cauchy_schwarz_sum a b
  simp only [Fin.sum_univ_two] at h
  exact h

/-! ## Applications and Corollaries -/

/-- **Triangle Inequality via Cauchy-Schwarz**

The triangle inequality ‖u + v‖ ≤ ‖u‖ + ‖v‖ can be proven using Cauchy-Schwarz.
Here we show the squared form: ‖u + v‖² ≤ (‖u‖ + ‖v‖)² -/
theorem triangle_sq_via_cauchy_schwarz {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) :
    ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
  have h_cs := cauchy_schwarz_inner u v
  have h_expand : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, v⟫_ℝ + ‖v‖ ^ 2 := norm_add_sq_real u v
  have h_target : (‖u‖ + ‖v‖) ^ 2 = ‖u‖ ^ 2 + 2 * (‖u‖ * ‖v‖) + ‖v‖ ^ 2 := by ring
  rw [h_expand, h_target]
  have : ⟪u, v⟫_ℝ ≤ |⟪u, v⟫_ℝ| := le_abs_self _
  linarith

/-- **Covariance Bound**

For centered random variables (represented as vectors), the correlation
coefficient is bounded by 1. This is a probabilistic interpretation of
Cauchy-Schwarz. -/
theorem covariance_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    |⟪u, v⟫_ℝ| / (‖u‖ * ‖v‖) ≤ 1 := by
  have h_pos : 0 < ‖u‖ * ‖v‖ := mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
  rw [div_le_one h_pos]
  exact cauchy_schwarz_inner u v

#check cauchy_schwarz_inner
#check cauchy_schwarz_two
#check cauchy_schwarz_sum
#check cauchy_schwarz_eq_iff_parallel

end CauchySchwarz
