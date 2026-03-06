/-
  Hölder's Inequality Equality Case
  Open Question: cauchy-schwarz-oq-03-oq-01

  Formalizes when equality holds in Hölder's (and Cauchy-Schwarz) inequality:

  Cauchy-Schwarz case (p = q = 2):
    (∑ f_i · g_i)² = (∑ f_i²)(∑ g_i²) iff f and g are proportional.
    Proved via Lagrange's identity: the double sum of squared cross-terms
    ∑_i ∑_j (f_i·g_j - f_j·g_i)² = 0 iff all cross-terms vanish.

  Inner product space case:
    |inner u v| = ‖u‖·‖v‖ iff ∃ c, u = c·v (Mathlib's norm_inner_eq_norm_iff).

  References:
  - Lagrange (1773): identity for 2×2 determinants
  - Hardy-Littlewood-Pólya "Inequalities" (1934) Ch. 2, Theorem 15
-/

import Mathlib

open Finset NNReal Real

namespace CauchySchwarzOQ03OQ01

-- ============================================================================
-- Part I: Finite Sum Equality via Lagrange Identity
-- ============================================================================

/-
From CauchySchwarzOQ03.lean, we have the Lagrange identity:
  ∑_i ∑_j (f_i·g_j - f_j·g_i)² = 2·[(∑f²)(∑g²) - (∑fg)²]

Equality in CS means (∑fg)² = (∑f²)(∑g²), so the Lagrange RHS = 0.
A sum of non-negative terms equals zero iff each term is zero.
So equality holds iff f_i·g_j = f_j·g_i for all i, j ∈ s.
-/

/-- Lagrange identity: the double sum of squared cross-terms equals
    twice the Cauchy-Schwarz deficit. -/
theorem lagrange_identity {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 =
      2 * ((∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) -
           (∑ i ∈ s, f i * g i) ^ 2) := by
  simp_rw [sub_sq, sum_add_distrib, Finset.sum_sub_distrib]
  have ha : ∑ i ∈ s, ∑ j ∈ s, (f i * g j) ^ 2 =
      (∑ i ∈ s, f i ^ 2) * (∑ j ∈ s, g j ^ 2) := by
    simp_rw [mul_pow, ← mul_sum, ← sum_mul]
  have hc : ∑ i ∈ s, ∑ j ∈ s, (f j * g i) ^ 2 =
      (∑ j ∈ s, f j ^ 2) * (∑ i ∈ s, g i ^ 2) := by
    rw [sum_comm]
    simp_rw [mul_pow, ← mul_sum, ← sum_mul]
  have hb : ∑ i ∈ s, ∑ j ∈ s, 2 * (f i * g j) * (f j * g i) =
      2 * (∑ i ∈ s, f i * g i) ^ 2 := by
    simp_rw [sq, sum_mul, mul_sum]
    congr 1; ext i; congr 1; ext j; ring
  rw [ha, hc, hb]; ring

/-- A sum of squares over a Finset is zero iff each term is zero. -/
theorem sum_sq_eq_zero_iff {ι : Type*} (s : Finset ι) (h : ι → ℝ) :
    ∑ i ∈ s, h i ^ 2 = 0 ↔ ∀ i ∈ s, h i = 0 := by
  constructor
  · intro hsum i hi
    have hnn : ∀ j ∈ s, 0 ≤ h j ^ 2 := fun j _ => sq_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i hi
    exact (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp this
  · intro hall
    exact Finset.sum_eq_zero fun i hi => by rw [hall i hi, sq, mul_zero]

/-- Double sum of squares is zero iff each term is zero. -/
theorem double_sum_sq_eq_zero_iff {ι : Type*} (s : Finset ι) (h : ι → ι → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, h i j ^ 2 = 0 ↔ ∀ i ∈ s, ∀ j ∈ s, h i j = 0 := by
  constructor
  · intro hsum i hi j hj
    have hnn_outer : ∀ k ∈ s, 0 ≤ ∑ l ∈ s, h k l ^ 2 :=
      fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _
    have h_inner_zero := (Finset.sum_eq_zero_iff_of_nonneg hnn_outer).mp hsum i hi
    exact (sum_sq_eq_zero_iff s (h i)).mp h_inner_zero j hj
  · intro hall
    exact Finset.sum_eq_zero fun i hi =>
      Finset.sum_eq_zero fun j hj => by rw [hall i hi j hj, sq, mul_zero]

/-- **Cauchy-Schwarz Equality Characterization (Finite Sums)**:
    Equality holds iff all cross-terms f_i·g_j - f_j·g_i vanish,
    which means f and g are "proportional" in the sense that
    f_i·g_j = f_j·g_i for all i, j. -/
theorem cauchy_schwarz_eq_iff {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 = (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) ↔
    ∀ i ∈ s, ∀ j ∈ s, f i * g j = f j * g i := by
  have h_lagrange := lagrange_identity s f g
  constructor
  · intro heq
    have h_zero : ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 = 0 := by
      linarith
    have h_all := (double_sum_sq_eq_zero_iff s (fun i j => f i * g j - f j * g i)).mp h_zero
    intro i hi j hj
    exact sub_eq_zero.mp (h_all i hi j hj)
  · intro hprop
    have h_zero : ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 = 0 :=
      (double_sum_sq_eq_zero_iff s _).mpr fun i hi j hj =>
        sub_eq_zero.mpr (hprop i hi j hj)
    linarith

-- ============================================================================
-- Part II: Proportionality from Cross-Term Condition
-- ============================================================================

/-
The condition ∀ i j, f_i·g_j = f_j·g_i means the 2×2 determinants vanish.
If some g_k ≠ 0, then f_i = (f_k/g_k)·g_i for all i.
-/

/-- If all cross-terms vanish and some g_k ≠ 0, then f = c · g
    where c = f_k / g_k. -/
theorem proportional_of_cross_terms_zero {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, f i * g j = f j * g i)
    {k : ι} (hk : k ∈ s) (hgk : g k ≠ 0) :
    ∀ i ∈ s, f i = (f k / g k) * g i := by
  intro i hi
  have h := hcross i hi k hk
  field_simp at h ⊢
  linarith

/-- **Full Cauchy-Schwarz Equality Characterization with Proportionality**:
    When g is not identically zero on s, equality holds iff f is a
    scalar multiple of g (proportional). -/
theorem cauchy_schwarz_eq_iff_proportional {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    {k : ι} (hk : k ∈ s) (hgk : g k ≠ 0) :
    (∑ i ∈ s, f i * g i) ^ 2 = (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) →
    ∃ c : ℝ, ∀ i ∈ s, f i = c * g i := by
  intro heq
  have hcross := cauchy_schwarz_eq_iff s f g |>.mp heq
  exact ⟨f k / g k, proportional_of_cross_terms_zero s f g hcross hk hgk⟩

-- ============================================================================
-- Part III: Inner Product Space Equality Case
-- ============================================================================

/-- **Cauchy-Schwarz equality for inner product spaces**:
    ‖inner u v‖ = ‖u‖·‖v‖ iff u and v are scalar multiples.
    This is the abstract version of the finite-sum equality case.
    (Uses Mathlib's norm_inner_eq_norm_iff.) -/
theorem cauchy_schwarz_eq_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖@inner ℝ _ _ u v‖ = ‖u‖ * ‖v‖ ↔ ∃ c : ℝ, u = c • v := by
  constructor
  · intro h
    obtain ⟨r, hr_ne, hr⟩ := (norm_inner_eq_norm_iff hu hv).mp h
    exact ⟨r⁻¹, by rw [hr, smul_smul, inv_mul_cancel₀ hr_ne, one_smul]⟩
  · intro ⟨c, hc⟩
    rw [hc, inner_smul_left, real_inner_self_eq_norm_sq, norm_smul]
    simp only [starRingEnd_apply, star_trivial, Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖v‖)]
    ring

/-- Corollary: absolute value form of the equality condition. -/
theorem cauchy_schwarz_abs_eq_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    |@inner ℝ _ _ u v| = ‖u‖ * ‖v‖ ↔ ∃ c : ℝ, u = c • v := by
  rw [← Real.norm_eq_abs]
  exact cauchy_schwarz_eq_inner u v hu hv

-- ============================================================================
-- Part IV: General Hölder Equality (Description)
-- ============================================================================

/-
## Summary of Equality Characterizations

### Cauchy-Schwarz (p = q = 2):
  (∑ f_i·g_i)² = (∑ f_i²)(∑ g_i²)
  ⟺ ∀ i,j ∈ s, f_i·g_j = f_j·g_i          (cross-term condition)
  ⟺ ∃ c, ∀ i ∈ s, f_i = c·g_i              (proportionality, when some g_i ≠ 0)

### Inner Product Space:
  ‖inner u v‖ = ‖u‖·‖v‖
  ⟺ ∃ c : ℝ, u = c • v                      (Mathlib's norm_inner_eq_norm_iff)

### General Hölder (p, q conjugate):
  ∑ f_i·g_i = ‖f‖_p · ‖g‖_q
  ⟺ ∃ λ ≥ 0, ∀ i, f_i^p = λ · g_i^q        (power proportionality)
  This follows from Young's equality: ab = a^p/p + b^q/q ⟺ a^p = b^q.
  The full formal proof of the general Hölder equality case requires
  showing that equality in ∑-Young implies pointwise equality,
  using the strict concavity of the logarithm.

### Equality in Integral Form:
  ∫ f·g dμ = ‖f‖_p · ‖g‖_q
  ⟺ ∃ λ ≥ 0, f^p = λ · g^q a.e.            (a.e. power proportionality)
-/

/-- Hölder's inequality (NNReal finite sums, from Mathlib). -/
theorem holder_nnreal {ι : Type*} (s : Finset ι) (f g : ι → ℝ≥0)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∑ i ∈ s, f i * g i ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) :=
  NNReal.inner_le_Lp_mul_Lq s f g hpq

/-- Cauchy-Schwarz for finite sums (consequence of Lagrange identity). -/
theorem cauchy_schwarz_finite {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) := by
  have h_nn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith [lagrange_identity s f g]

/-- Concrete example: equality when vectors are proportional.
    f = (1, 2, 3), g = (2, 4, 6) = 2·f, so equality holds. -/
example : (1*2 + 2*4 + 3*6 : ℝ)^2 = (1^2 + 2^2 + 3^2) * (2^2 + 4^2 + 6^2) := by
  norm_num

/-- Concrete example: strict inequality when not proportional.
    f = (1, 0), g = (0, 1), inner product = 0 < 1 = ‖f‖·‖g‖. -/
example : (1*0 + 0*1 : ℝ)^2 < (1^2 + 0^2) * (0^2 + 1^2) := by
  norm_num

end CauchySchwarzOQ03OQ01
