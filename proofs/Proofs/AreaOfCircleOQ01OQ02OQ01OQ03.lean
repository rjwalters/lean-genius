/-
  Thin Shell Limit: ω_n → 0 as n → ∞
  Open Question: area-of-circle-oq-01-oq-02-oq-01-oq-03

  The unit n-ball volume ω_n = π^(n/2) / Γ(n/2 + 1) converges to 0 as n → ∞.

  This is a fundamental fact in high-dimensional geometry: the volume of the
  unit ball vanishes in high dimensions. Equivalently, most of the volume of
  a high-dimensional ball concentrates near its boundary (the "thin shell"
  phenomenon).

  Proof strategy:
  1. Recurrence: ω_{n+2} = (2π/(n+2)) · ω_n (from Γ(z+1) = z·Γ(z))
  2. Ratio bound: For n ≥ 8, 2π/(n+2) ≤ 2/3 (since 3π < 10 ≤ n+2)
  3. Geometric decrease: ω_{n₀+2k} ≤ (2/3)^k · ω_{n₀} (induction using step 2)
  4. Main theorem: 0 ≤ ω_n ≤ C·(2/3)^k → 0 (squeeze with geometric bound)

  Chain: area-of-circle → OQ01 → OQ02 → OQ01 → OQ03 (THIS FILE)

  References:
  - AreaOfCircleOQ01OQ02OQ01OQ01.lean (sibling: proves recurrence)
  - https://en.wikipedia.org/wiki/Volume_of_an_n-ball#Low_dimensions
-/

import Mathlib

open Real Filter Topology

noncomputable section

namespace ThinShellLimit

/- ## Part I: Definition and Basic Properties -/

/-- The unit n-ball volume ω_n = π^(n/2) / Γ(n/2 + 1).
    For n=0: 1, n=1: 2, n=2: π, n=3: 4π/3, n=4: π²/2, n=5: 8π²/15, ... -/
def ω (n : ℕ) : ℝ :=
  π ^ ((n : ℝ) / 2) / Gamma ((n : ℝ) / 2 + 1)

/-- ω_n > 0 for all n. -/
theorem omega_pos (n : ℕ) : 0 < ω n := by
  unfold ω
  apply div_pos
  · exact rpow_pos_of_pos pi_pos _
  · exact Gamma_pos_of_pos (by positivity)

/-- ω_n ≥ 0 for all n (weaker version for convenience). -/
theorem omega_nonneg (n : ℕ) : 0 ≤ ω n :=
  le_of_lt (omega_pos n)

/-- The two-step recurrence: ω_{n+2} = (2π/(n+2)) · ω_n.
    Follows from Γ(z+1) = z·Γ(z) and π^((n+2)/2) = π · π^(n/2).
    (Reproduced from sibling OQ01 for self-containedness.) -/
theorem omega_recurrence (n : ℕ) :
    ω (n + 2) = 2 * π / (↑n + 2) * ω n := by
  unfold ω
  have hcast1 : (↑(n + 2) : ℝ) / 2 = ↑n / 2 + 1 := by push_cast; ring
  have hcast2 : (↑(n + 2) : ℝ) / 2 + 1 = ↑n / 2 + 2 := by push_cast; ring
  rw [hcast1, hcast2, rpow_add pi_pos, rpow_one]
  have hpos : (0 : ℝ) < ↑n / 2 + 1 := by positivity
  rw [show (↑n : ℝ) / 2 + 2 = (↑n / 2 + 1) + 1 from by ring,
      Gamma_add_one hpos.ne']
  have hΓ : 0 < Gamma (↑n / 2 + 1) := Gamma_pos_of_pos (by positivity)
  field_simp [hpos.ne', hΓ.ne']
  ring

/- ## Part II: Ratio Bound -/

/-- For n ≥ 8, the recurrence ratio 2π/(n+2) is at most 2/3.
    Proof: 3π < 10 (since π < 3.1416) and n+2 ≥ 10. -/
theorem ratio_le_two_thirds (n : ℕ) (hn : 8 ≤ n) :
    2 * π / (↑n + 2) ≤ 2 / 3 := by
  rw [div_le_div_iff (by positivity : (0 : ℝ) < ↑n + 2) (by norm_num : (0 : ℝ) < 3)]
  -- Goal: 6π ≤ 2n + 4. From π < 10/3: 6π < 20. From n ≥ 8: 2n + 4 ≥ 20.
  have hπ : π < 10 / 3 := by linarith [pi_lt_3141593]
  have hn' : (8 : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast hn
  linarith

/-- For n ≥ 8, ω_{n+2} ≤ (2/3) · ω_n (geometric decay step). -/
theorem omega_decrease (n : ℕ) (hn : 8 ≤ n) :
    ω (n + 2) ≤ 2 / 3 * ω n := by
  rw [omega_recurrence]
  exact mul_le_mul_of_nonneg_right (ratio_le_two_thirds n hn) (omega_nonneg n)

/- ## Part III: Geometric Decrease by Induction -/

/-- Starting from any n₀ ≥ 8, the two-step subsequence decreases geometrically:
    ω(n₀ + 2k) ≤ (2/3)^k · ω(n₀). -/
theorem omega_geometric_bound (n₀ : ℕ) (hn₀ : 8 ≤ n₀) (k : ℕ) :
    ω (n₀ + 2 * k) ≤ (2 / 3) ^ k * ω n₀ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_eq : n₀ + 2 * (k + 1) = (n₀ + 2 * k) + 2 := by omega
    rw [h_eq]
    calc ω ((n₀ + 2 * k) + 2)
        ≤ 2 / 3 * ω (n₀ + 2 * k) := omega_decrease _ (by omega)
      _ ≤ 2 / 3 * ((2 / 3) ^ k * ω n₀) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2 / 3) ^ (k + 1) * ω n₀ := by rw [pow_succ]; ring

/- ## Part IV: Main Theorem -/

/-- **MAIN THEOREM**: The unit n-ball volume ω_n converges to 0 as n → ∞.

    This is the thin shell limit: in high dimensions, the volume of the unit
    ball vanishes. Most volume concentrates near the boundary.

    Proof: The recurrence ω_{n+2} = (2π/(n+2))·ω_n gives geometric decrease
    for n ≥ 8 (ratio ≤ 2/3), and the geometric bound tends to 0. -/
theorem tendsto_omega_zero : Tendsto (fun n => ω n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- M bounds the base cases
  set M := max (ω 8) (ω 9) with hM_def
  have hM_pos : 0 < M := lt_max_of_lt_left (omega_pos 8)
  -- Find K such that (2/3)^K · M < ε
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (div_pos hε hM_pos) (by norm_num : (2 : ℝ) / 3 < 1)
  have hKε : (2 / 3) ^ K * M < ε := by rwa [div_lt_iff hM_pos] at hK
  -- N = 9 + 2K suffices
  refine ⟨9 + 2 * K, fun n hn => ?_⟩
  simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (omega_nonneg n)]
  -- Split into even/odd
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- Even: n = m + m (or n = 2m)
    have hm_ge : K + 4 ≤ m := by omega
    have h_eq : n = 8 + 2 * (m - 4) := by omega
    rw [h_eq]
    calc ω (8 + 2 * (m - 4))
        ≤ (2 / 3) ^ (m - 4) * ω 8 := omega_geometric_bound 8 le_rfl (m - 4)
      _ ≤ (2 / 3) ^ K * ω 8 := by
          apply mul_le_mul_of_nonneg_right _ (omega_nonneg 8)
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ (2 / 3) ^ K * M := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) K)
          exact le_max_left _ _
      _ < ε := hKε
  · -- Odd: n = 2 * m + 1
    have hm_ge : K + 4 ≤ m := by omega
    have h_eq : n = 9 + 2 * (m - 4) := by omega
    rw [h_eq]
    calc ω (9 + 2 * (m - 4))
        ≤ (2 / 3) ^ (m - 4) * ω 9 := omega_geometric_bound 9 (by norm_num) (m - 4)
      _ ≤ (2 / 3) ^ K * ω 9 := by
          apply mul_le_mul_of_nonneg_right _ (omega_nonneg 9)
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ (2 / 3) ^ K * M := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) K)
          exact le_max_right _ _
      _ < ε := hKε

/- ## Part V: Thin Shell Concentration -/

/-- In high dimensions, the fraction of volume within distance ε of the boundary
    approaches 1. That is, 1 - (1-ε)^n → 1 as n → ∞ for any 0 < ε < 1.

    This follows directly from scaling V_n(r) = ω_n · r^n:
    V_n((1-ε)r) / V_n(r) = (1-ε)^n → 0, so the shell fraction → 1. -/
theorem thin_shell_concentration (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n => 1 - (1 - ε) ^ n) atTop (𝓝 1) := by
  have h_base_nn : 0 ≤ 1 - ε := by linarith
  have h_base_lt : 1 - ε < 1 := by linarith
  have h_pow := tendsto_pow_atTop_nhds_zero_of_lt_one h_base_nn h_base_lt
  have h := tendsto_const_nhds.sub h_pow
  simp only [sub_zero] at h
  exact h

/- ## Part VI: Summary

### Proved (0 sorries, 0 axioms):
1. `omega_pos` — ω_n > 0 for all n
2. `omega_recurrence` — ω_{n+2} = (2π/(n+2)) · ω_n
3. `ratio_le_two_thirds` — 2π/(n+2) ≤ 2/3 for n ≥ 8
4. `omega_decrease` — ω_{n+2} ≤ (2/3) · ω_n for n ≥ 8
5. `omega_geometric_bound` — ω_{n₀+2k} ≤ (2/3)^k · ω_{n₀} for n₀ ≥ 8
6. `tendsto_omega_zero` — ω_n → 0 (**MAIN THEOREM**)
7. `thin_shell_concentration` — 1 - (1-ε)^n → 1 for 0 < ε < 1

### Mathematical Significance:
The vanishing of unit ball volume in high dimensions is a cornerstone of
high-dimensional geometry and probability. Key consequences include:
- Concentration of measure on the sphere
- The "curse of dimensionality" in statistics and machine learning
- Gaussian behavior emerges from uniform distributions on high-dimensional balls

### Answer to the OQ:
YES, the thin shell limit holds: ω_n = π^(n/2)/Γ(n/2+1) → 0 as n → ∞.
The proof uses the two-step recurrence ω_{n+2} = (2π/(n+2))·ω_n, combined
with the observation that the ratio eventually drops below 2/3, giving
geometric convergence to 0.
-/

end ThinShellLimit

end
