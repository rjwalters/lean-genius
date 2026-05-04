import Mathlib
import Proofs.BuffonsNeedleOQ01OQ01OQ04

/-
  The Cauchy–Crofton Constant Decays to Zero
  Open Question: buffons-needle-oq-01-oq-01-oq-04-oq-01

  Proves cauchyCroftonConst n → 0 as n → ∞.

  ## Strategy

  1. **Two-step recurrence**: c_{n+2} = c_n · n/(n+1) from sphereArea_recurrence.
  2. **Upper bound**: c_n ≤ 2/√(nπ) for n ≥ 2, by induction using the recurrence.
     - Inductive step: c_{n+2} = c_n · n/(n+1) ≤ 2/√(nπ) · n/(n+1) ≤ 2/√((n+2)π).
     - The last step squares to n(n+2) ≤ (n+1)² (AM-GM).
  3. **Squeeze**: 0 ≤ c_n ≤ 2/√(nπ) → 0.

  Bases: c_2 = 2/π ≤ 2/√(2π) (since π > 2 → π > √(2π));
         c_3 = 1/2 ≤ 2/√(3π) (since π < 4 → 3π < 12 < 16 = 4² → √(3π) < 4).

  Parent: BuffonsNeedleOQ01OQ01OQ04.lean
  References: Cauchy (1832/1841), Crofton (1868), Santaló (1976) Ch. 14.
-/

open Real CauchyCrofton Filter Topology

namespace CauchyCroftonDecay

/-! ### Two-Step Recurrence -/

/-- c_{n+2} = c_n · n/(n+1) for n ≥ 2, from the sphere area recurrence. -/
lemma cauchyCrofton_step (n : ℕ) (hn : 2 ≤ n) :
    cauchyCroftonConst (n + 2) = cauchyCroftonConst n * ((n : ℝ) / ((n : ℝ) + 1)) := by
  unfold cauchyCroftonConst
  have h1 : (n + 2 : ℕ) - 2 = n := by omega
  have h2 : (n + 2 : ℕ) - 1 = n + 1 := by omega
  simp only [h1, h2]
  have hrec_n : sphereArea n = 2 * π / ((n : ℝ) - 1) * sphereArea (n - 2) :=
    sphereArea_recurrence n hn
  have hrec_n1 : sphereArea (n + 1) = 2 * π / (n : ℝ) * sphereArea (n - 1) := by
    have hrec := sphereArea_recurrence (n + 1) (by omega)
    simp only [show (n + 1 : ℕ) - 2 = n - 1 from by omega] at hrec
    have hcast : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
    rw [hcast] at hrec; exact hrec
  rw [hrec_n, hrec_n1]
  have hnn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn1, hnn, hnn1, (sphereArea_pos (n - 2)).ne', (sphereArea_pos (n - 1)).ne',
              pi_pos.ne']
  ring

/-! ### Key Geometric Inequality -/

/-- n · √((n+2)π) ≤ (n+1) · √(nπ), proved by squaring: n(n+2) ≤ (n+1)². -/
private lemma sqrt_ratio_bound (n : ℕ) :
    (n : ℝ) * sqrt (((n : ℝ) + 2) * π) ≤ ((n : ℝ) + 1) * sqrt ((n : ℝ) * π) := by
  have hlhs : (0 : ℝ) ≤ (n : ℝ) * sqrt (((n : ℝ) + 2) * π) := by positivity
  have hrhs : (0 : ℝ) ≤ ((n : ℝ) + 1) * sqrt ((n : ℝ) * π) := by positivity
  rw [← sqrt_sq hlhs, ← sqrt_sq hrhs]
  apply sqrt_le_sqrt
  rw [mul_pow, mul_pow, sq_sqrt (by positivity), sq_sqrt (by positivity)]
  have key : n * (n + 2) ≤ (n + 1) ^ 2 := by nlinarith [n.zero_le]
  have key_r : (n : ℝ) * ((n : ℝ) + 2) ≤ ((n : ℝ) + 1) ^ 2 := by exact_mod_cast key
  nlinarith [pi_pos]

/-! ### Upper Bound by Induction -/

/-- c_n ≤ 2/√(nπ) for all n ≥ 2, proved by separate inductions
    on even (2+2k) and odd (3+2k) subsequences. -/
lemma cauchyCrofton_upper_bound (n : ℕ) (hn : 2 ≤ n) :
    cauchyCroftonConst n ≤ 2 / sqrt ((n : ℝ) * π) := by
  suffices h : ∀ k : ℕ,
      cauchyCroftonConst (2 + 2 * k) ≤ 2 / sqrt (((2 + 2 * k : ℕ) : ℝ) * π) ∧
      cauchyCroftonConst (3 + 2 * k) ≤ 2 / sqrt (((3 + 2 * k : ℕ) : ℝ) * π) by
    -- Decompose n into 2+2k or 3+2k form
    have hn_ge : ∃ k : ℕ, (n = 2 + 2 * k ∨ n = 3 + 2 * k) := by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- n = k + k ≥ 2, so k ≥ 1
        cases k with
        | zero => omega
        | succ k' => exact ⟨k', Or.inl (by omega)⟩
      · -- n = 2*k + 1 ≥ 2, so k ≥ 1
        cases k with
        | zero => omega
        | succ k' => exact ⟨k', Or.inr (by omega)⟩
    obtain ⟨k, hk | hk⟩ := hn_ge <;> subst hk <;>
      [exact (h k).1; exact (h k).2]
  -- Prove the bound for both parities simultaneously by induction on k
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · -- c_2 = 2/π ≤ 2/√(2π): need √(2π) ≤ π, i.e., 2π ≤ π² (since π > 2)
      simp only [show 2 + 2 * 0 = 2 from rfl]
      rw [cauchyCrofton_two, div_le_div_iff pi_pos (sqrt_pos.mpr (by positivity))]
      nlinarith [sq_sqrt (show (0:ℝ) ≤ 2 * π by positivity), sqrt_nonneg (2 * π), pi_gt_three]
    · -- c_3 = 1/2 ≤ 2/√(3π): need √(3π) ≤ 4, i.e., 3π ≤ 16 (since π < 4)
      simp only [show 3 + 2 * 0 = 3 from rfl]
      rw [cauchyCrofton_three, div_le_div_iff (by norm_num : (0:ℝ) < 2)
          (sqrt_pos.mpr (by positivity))]
      nlinarith [sq_sqrt (show (0:ℝ) ≤ 3 * π by positivity), sqrt_nonneg (3 * π), pi_lt_four]
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · -- Even step: c_{2+2(k+1)} = c_{(2+2k)+2} ≤ 2/√((2+2(k+1))π)
      have heq : 2 + 2 * (k + 1) = (2 + 2 * k) + 2 := by omega
      rw [heq, cauchyCrofton_step _ (by omega)]
      apply le_trans (mul_le_mul_of_nonneg_right ih.1 (by positivity))
      rw [show ((2 + 2 * (k + 1) : ℕ) : ℝ) = ((2 + 2 * k : ℕ) : ℝ) + 2 from by push_cast; ring,
          div_mul_div_comm,
          div_le_div_iff (by positivity) (sqrt_pos.mpr (by positivity))]
      have bound := sqrt_ratio_bound (2 + 2 * k)
      push_cast at bound ⊢; linarith
    · -- Odd step: c_{3+2(k+1)} = c_{(3+2k)+2} ≤ 2/√((3+2(k+1))π)
      have heq : 3 + 2 * (k + 1) = (3 + 2 * k) + 2 := by omega
      rw [heq, cauchyCrofton_step _ (by omega)]
      apply le_trans (mul_le_mul_of_nonneg_right ih.2 (by positivity))
      rw [show ((3 + 2 * (k + 1) : ℕ) : ℝ) = ((3 + 2 * k : ℕ) : ℝ) + 2 from by push_cast; ring,
          div_mul_div_comm,
          div_le_div_iff (by positivity) (sqrt_pos.mpr (by positivity))]
      have bound := sqrt_ratio_bound (3 + 2 * k)
      push_cast at bound ⊢; linarith

/-! ### Main Theorem -/

/-- **The Cauchy–Crofton constant decays to zero**: c_n → 0 as n → ∞.

    Proof by squeeze: 0 ≤ c_n ≤ 2/√(nπ) for n ≥ 2, and 2/√(nπ) → 0.

    The upper bound uses c_{n+2} = c_n · n/(n+1) (two-step recurrence) and
    n/(n+1) ≤ √n/√(n+2) (from AM-GM: n(n+2) ≤ (n+1)²). -/
theorem cauchyCroftonConst_tendsto_zero :
    Tendsto cauchyCroftonConst atTop (nhds 0) := by
  -- Upper bound sequence: 2/√(nπ) → 0
  have hg : Tendsto (fun n : ℕ => 2 / sqrt ((n : ℝ) * π)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) * π) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const pi_pos
    have h2 : Tendsto (fun n : ℕ => sqrt ((n : ℝ) * π)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp h1
    have h3 : Tendsto (fun n : ℕ => (sqrt ((n : ℝ) * π))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp h2
    have h4 : Tendsto (fun n : ℕ => 2 * (sqrt ((n : ℝ) * π))⁻¹) atTop (nhds 0) := by
      have := h3.const_mul 2; simpa using this
    exact h4.congr (fun n => by rw [mul_comm, ← div_eq_mul_inv])
  -- Apply squeeze theorem (eventually for n ≥ 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg
  · exact eventually_atTop.mpr ⟨2, fun n hn => (cauchyCroftonConst_pos n hn).le⟩
  · exact eventually_atTop.mpr ⟨2, fun n hn => cauchyCrofton_upper_bound n hn⟩

end CauchyCroftonDecay
