/-
  Weighted Cauchy-Schwarz for Finite Sum Inner Products
  Open Question: cauchy-schwarz-oq-04-oq-01

  Proves: (Σ wᵢ aᵢ bᵢ)² ≤ (Σ wᵢ aᵢ²)(Σ wᵢ bᵢ²) for positive wᵢ.
  Also proves Titu's lemma: (Σ aᵢ)²/(Σ bᵢ) ≤ Σ aᵢ²/bᵢ for positive bᵢ.

  References:
  - Cauchy (1821), Schwarz (1885)
  - Steele "The Cauchy-Schwarz Master Class" (2004)
-/

import Mathlib

namespace CauchySchwarzOQ04OQ01

open Finset BigOperators

-- ============================================================================
-- Part I: Cauchy-Schwarz for Finite Sums (quadratic discriminant proof)
-- ============================================================================

/-- Cauchy-Schwarz for finite sums: (Σ aᵢ bᵢ)² ≤ (Σ aᵢ²)(Σ bᵢ²).
    Proof: The quadratic Q(t) = Σ(t·aᵢ + bᵢ)² ≥ 0 for all t.
    Expanding: Q(t) = t²·Σaᵢ² + 2t·Σaᵢbᵢ + Σbᵢ² ≥ 0.
    Discriminant ≤ 0 gives the result. -/
theorem cauchy_schwarz_sum {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i, a i * b i) ^ 2 ≤ (∑ i, a i ^ 2) * (∑ i, b i ^ 2) := by
  -- Use Mathlib: Finset.inner_mul_le_norm_mul_sq or the discriminant approach.
  -- The key is that 0 ≤ Σ(t·aᵢ + bᵢ)² for all t ∈ ℝ.
  have hQ : ∀ t : ℝ, 0 ≤ ∑ i : Fin n, (t * a i + b i) ^ 2 :=
    fun t => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  -- Expand: Q(t) = (Σaᵢ²)t² + 2(Σaᵢbᵢ)t + Σbᵢ²
  have hexpand : ∀ t : ℝ, ∑ i : Fin n, (t * a i + b i) ^ 2 =
      (∑ i, a i ^ 2) * t ^ 2 + 2 * (∑ i, a i * b i) * t + ∑ i, b i ^ 2 := by
    intro t
    have : ∀ i : Fin n, (t * a i + b i) ^ 2 =
        a i ^ 2 * t ^ 2 + 2 * (a i * b i) * t + b i ^ 2 := by intro i; ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  -- Nonneg quadratic ⟹ discriminant ≤ 0
  by_cases hA : ∑ i, a i ^ 2 = 0
  · -- If Σaᵢ² = 0 then each aᵢ = 0, so Σaᵢbᵢ = 0
    have ha_zero : ∀ i, a i = 0 := by
      intro i
      have h1 : a i ^ 2 ≤ ∑ j, a j ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)
      have h2 : (∑ j, a j ^ 2) = 0 := hA
      have h3 : a i ^ 2 = 0 := le_antisymm (h2 ▸ h1) (sq_nonneg _)
      exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h3
    simp [ha_zero]
  · -- Σaᵢ² > 0: take t = -(Σaᵢbᵢ) / (Σaᵢ²)
    have hA_pos : 0 < ∑ i, a i ^ 2 := by
      rcases lt_or_eq_of_le (Finset.sum_nonneg (fun i _ => sq_nonneg (a i))) with h | h
      · exact h
      · exact absurd h.symm hA
    specialize hQ (-(∑ i, a i * b i) / (∑ i, a i ^ 2))
    rw [hexpand] at hQ
    -- After substitution: Q(-S/A) = A·(S/A)² - 2S·(S/A) + B = B - S²/A ≥ 0
    -- So S² ≤ A·B
    have h_key : (∑ i, a i ^ 2) * (-(∑ i, a i * b i) / (∑ i, a i ^ 2)) ^ 2 +
        2 * (∑ i, a i * b i) * (-(∑ i, a i * b i) / (∑ i, a i ^ 2)) +
        (∑ i, b i ^ 2) =
        (∑ i, b i ^ 2) - (∑ i, a i * b i) ^ 2 / (∑ i, a i ^ 2) := by
      field_simp; ring
    rw [h_key] at hQ
    -- 0 ≤ B - S²/A, so S² ≤ A·B
    rw [sub_nonneg] at hQ
    -- hQ : (Σ aᵢ bᵢ)² / (Σ aᵢ²) ≤ Σ bᵢ²
    -- Want: (Σ aᵢ bᵢ)² ≤ (Σ aᵢ²) * (Σ bᵢ²)
    calc (∑ i, a i * b i) ^ 2
        = (∑ i, a i * b i) ^ 2 / (∑ i, a i ^ 2) * (∑ i, a i ^ 2) := by
          field_simp
      _ ≤ (∑ i, b i ^ 2) * (∑ i, a i ^ 2) := by
          exact mul_le_mul_of_nonneg_right hQ (le_of_lt hA_pos)
      _ = (∑ i, a i ^ 2) * (∑ i, b i ^ 2) := by ring

-- ============================================================================
-- Part II: Weighted Cauchy-Schwarz
-- ============================================================================

/-- **Weighted Cauchy-Schwarz**: (Σ wᵢ aᵢ bᵢ)² ≤ (Σ wᵢ aᵢ²)(Σ wᵢ bᵢ²). -/
theorem weighted_cauchy_schwarz {n : ℕ} (w a b : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    (∑ i, w i * a i * b i) ^ 2 ≤
    (∑ i, w i * a i ^ 2) * (∑ i, w i * b i ^ 2) := by
  let a' : Fin n → ℝ := fun i => Real.sqrt (w i) * a i
  let b' : Fin n → ℝ := fun i => Real.sqrt (w i) * b i
  have hsq : ∀ i, Real.sqrt (w i) * Real.sqrt (w i) = w i :=
    fun i => Real.mul_self_sqrt (le_of_lt (hw i))
  have key_ab : ∀ i, w i * a i * b i = a' i * b' i := by
    intro i; show w i * a i * b i = (Real.sqrt (w i) * a i) * (Real.sqrt (w i) * b i)
    have h := hsq i
    -- (√w * a) * (√w * b) = √w * √w * a * b = w * a * b
    have : (Real.sqrt (w i) * a i) * (Real.sqrt (w i) * b i) =
        Real.sqrt (w i) * Real.sqrt (w i) * (a i * b i) := by ring
    rw [this, h]; ring
  have key_a2 : ∀ i, w i * a i ^ 2 = a' i ^ 2 := by
    intro i; show w i * a i ^ 2 = (Real.sqrt (w i) * a i) ^ 2
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hw i))]
  have key_b2 : ∀ i, w i * b i ^ 2 = b' i ^ 2 := by
    intro i; show w i * b i ^ 2 = (Real.sqrt (w i) * b i) ^ 2
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hw i))]
  calc (∑ i, w i * a i * b i) ^ 2
      = (∑ i, a' i * b' i) ^ 2 := by
        congr 1; exact Finset.sum_congr rfl (fun i _ => key_ab i)
    _ ≤ (∑ i, a' i ^ 2) * (∑ i, b' i ^ 2) := cauchy_schwarz_sum a' b'
    _ = (∑ i, w i * a i ^ 2) * (∑ i, w i * b i ^ 2) := by
        congr 1
        · exact Finset.sum_congr rfl (fun i _ => (key_a2 i).symm)
        · exact Finset.sum_congr rfl (fun i _ => (key_b2 i).symm)

-- ============================================================================
-- Part III: Titu's Lemma
-- ============================================================================

/-- **Titu's Lemma**: (Σ aᵢ)²/(Σ bᵢ) ≤ Σ aᵢ²/bᵢ for positive bᵢ. -/
theorem titu_lemma {n : ℕ} (a b : Fin n → ℝ) (hb : ∀ i, 0 < b i)
    (hB : 0 < ∑ i, b i) :
    (∑ i, a i) ^ 2 / (∑ i, b i) ≤ ∑ i, a i ^ 2 / b i := by
  rw [div_le_iff₀ hB]
  let f : Fin n → ℝ := fun i => a i / Real.sqrt (b i)
  let g : Fin n → ℝ := fun i => Real.sqrt (b i)
  have hcs := cauchy_schwarz_sum f g
  have hfg : (∑ i, f i * g i) = ∑ i, a i := by
    apply Finset.sum_congr rfl; intro i _
    show a i / Real.sqrt (b i) * Real.sqrt (b i) = a i
    exact div_mul_cancel₀ _ (Real.sqrt_ne_zero'.mpr (hb i))
  have hf2 : (∑ i, f i ^ 2) = ∑ i, a i ^ 2 / b i := by
    apply Finset.sum_congr rfl; intro i _
    show (a i / Real.sqrt (b i)) ^ 2 = a i ^ 2 / b i
    rw [div_pow, Real.sq_sqrt (le_of_lt (hb i))]
  have hg2 : (∑ i, g i ^ 2) = ∑ i, b i := by
    apply Finset.sum_congr rfl; intro i _
    show Real.sqrt (b i) ^ 2 = b i
    exact Real.sq_sqrt (le_of_lt (hb i))
  rw [hfg, hf2, hg2] at hcs; linarith

-- ============================================================================
-- Part IV: Sum Positivity
-- ============================================================================

/-- Weighted sums of squares are nonneg. -/
theorem weighted_sum_sq_nonneg {n : ℕ} (w a : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ ∑ i, w i * a i ^ 2 :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))

#check cauchy_schwarz_sum
#check weighted_cauchy_schwarz
#check titu_lemma

end CauchySchwarzOQ04OQ01
