/-
  Aristotle targets for Roth's Theorem Quantitative Bounds
  Supporting analysis and density lemmas for automated proof search.
  See RothTheoremQuantitative.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main quantitative bounds (Roth, Behrend, Kelley-Meka)
  - Routine arithmetic and analytic facts about density and AP-free sets
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace RothTheoremQuantitativeAristotle

open Real Finset Filter

-- ═══════════════════════════════════════════════════════════════════
-- PART I: Density Arithmetic
-- ═══════════════════════════════════════════════════════════════════

/-- If δ > 0, then δ² > 0. -/
theorem delta_sq_pos (delta : ℝ) (hdelta : 0 < delta) : 0 < delta ^ 2 := by
  positivity

/-- If δ > 0, then 100 / δ² > 0. -/
theorem density_bound_pos (delta : ℝ) (hdelta : 0 < delta) : 0 < 100 / delta ^ 2 := by
  positivity

/-- The density increment formula: δ + k * δ² / 100 is increasing in k. -/
theorem density_increment_mono (delta : ℝ) (hdelta : 0 < delta) (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) :
    delta + k₁ * delta ^ 2 / 100 ≤ delta + k₂ * delta ^ 2 / 100 := by
  gcongr
  exact_mod_cast h

/-- After at most ⌊100/δ²⌋ density increments, the density exceeds 1. -/
theorem density_exceeds_one_after_floor (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ k : ℕ, k ≤ ⌊100 / delta ^ 2⌋₊ + 1 ∧ delta + k * delta ^ 2 / 100 > 1 := by
  refine ⟨⌊100 / delta ^ 2⌋₊ + 1, le_refl _, ?_⟩
  have hd2 : 0 < delta ^ 2 := by positivity
  have hk : (100 / delta ^ 2 : ℝ) < (⌊100 / delta ^ 2⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  push_cast
  nlinarith [sq_nonneg delta]

/-- The Roth iteration count ⌊100/δ²⌋ is monotone: smaller δ gives more iterations. -/
theorem iteration_count_antimono (delta₁ delta₂ : ℝ) (h₁ : 0 < delta₁) (h₂ : 0 < delta₂)
    (h : delta₁ ≤ delta₂) : ⌊100 / delta₂ ^ 2⌋₊ ≤ ⌊100 / delta₁ ^ 2⌋₊ := by
  apply Nat.floor_le_floor
  have hsq : delta₁ ^ 2 ≤ delta₂ ^ 2 := by nlinarith [sq_nonneg (delta₂ - delta₁)]
  exact div_le_div_of_le_left (by positivity) (by positivity) hsq

/-- For δ = 1/√(log N), 100/δ² = 100 * log N. -/
theorem roth_iteration_count_formula (N : ℕ) (hN : 2 < N) :
    100 / (1 / sqrt (log N)) ^ 2 = 100 * log N := by
  have hlogN : 0 < log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsqrt : sqrt (log N) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlogN)
  rw [div_pow, one_pow, sq_sqrt hlogN.le]
  field_simp

-- ═══════════════════════════════════════════════════════════════════
-- PART II: AP-Freeness Properties
-- ═══════════════════════════════════════════════════════════════════

/-- AP-freeness is closed under taking subsets (in ZMod N). -/
theorem apFree_mono {N : ℕ} {A B : Finset (ZMod N)}
    (hAB : B ⊆ A)
    (hA : ∀ a d : ZMod N, d ≠ 0 → a ∈ A → a + d ∈ A → a + 2 * d ∉ A) :
    ∀ a d : ZMod N, d ≠ 0 → a ∈ B → a + d ∈ B → a + 2 * d ∉ B :=
  fun a d hd ha had hadd => hA a d hd (hAB ha) (hAB had) (hAB hadd)

/-- A 2-element AP-free set: {0, 1} in ZMod N for N ≥ 3. -/
theorem two_element_ap_free (N : ℕ) (hN : 3 ≤ N) :
    ∀ a d : ZMod N, d ≠ 0 → a ∈ ({0, 1} : Finset (ZMod N)) →
    a + d ∈ ({0, 1} : Finset (ZMod N)) → a + 2 * d ∉ ({0, 1} : Finset (ZMod N)) := by
  sorry

-- NOTE: rothNumber_ge_half (r₃(N) ≥ ⌊N/2⌋) was REMOVED — it is FALSE for large N.
-- By Roth's theorem, r₃(N)/N → 0, so r₃(N) < N/2 for sufficiently large N.

-- ═══════════════════════════════════════════════════════════════════
-- PART III: Logarithmic Growth Facts
-- ═══════════════════════════════════════════════════════════════════

/-- log N → ∞ as N → ∞. -/
theorem log_nat_tendsto_atTop :
    Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- For N ≥ 3, log(log N) > 0. -/
theorem log_log_pos (N : ℕ) (hN : 3 ≤ N) : 0 < Real.log (Real.log N) := by
  have hN_real : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hN1 : 1 < Real.log N := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le he hN_real)
  exact Real.log_pos hN1

/-- N / log(log N) → ∞ as N → ∞. -/
theorem n_div_log_log_tendsto_atTop :
    Tendsto (fun N : ℕ => (N : ℝ) / Real.log (Real.log N)) atTop atTop := by
  sorry

/-- For c > 0, N · exp(-c · √(log N)) is eventually greater than any constant. -/
theorem behrend_lower_eventually_large (c : ℝ) (hc : 0 < c) (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, K < N * Real.exp (-c * Real.sqrt (Real.log N)) := by
  sorry

/-- The Behrend exponent satisfies: exp(-c√(log N)) → 1 relative to polynomial growth. -/
theorem behrend_exponent_vs_poly (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.exp (-c * Real.sqrt (Real.log N)) ≥ (N : ℝ) ^ (-ε) := by
  sorry

end RothTheoremQuantitativeAristotle
