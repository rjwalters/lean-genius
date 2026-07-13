import Proofs.BetaCentralBinomialAsymptotic
import Proofs.BetaDiagEffectiveRate
import Mathlib

/-
# An Effective Two-Sided Rate for the Central Binomial Coefficient

## What This Proves (research node `beta-central-binomial-asymptotic-oq-01`)

The parent entry `BetaCentralBinomialAsymptotic` proves the **bare asymptotic
equivalence**

  `C(2n, n) ~ 4ⁿ / √(πn)`   (`centralBinom_isEquivalent`),

an `atTop` statement with no control for any fixed `n`.  The open question asks:

  *Can the bare equivalence be upgraded to an effective two-sided rate with
  explicit constants valid for all `n`?*

This file answers **yes**, giving explicit numerical constants that pin the
central binomial coefficient to its Stirling scale `4ⁿ/√(πn)` for **every**
`n ≥ 1`:

  **`centralBinom_effective_rate`** :
    `(2π/e²) · 4ⁿ/√(πn)  ≤  C(2n, n)  ≤  (e/√(2π)) · 4ⁿ/√(πn)`   (all `n ≥ 1`).

Numerically `2π/e² ≈ 0.8503` and `e/√(2π) ≈ 1.0844`, so `C(2n,n)` never strays
more than ~15%/~8.5% from the leading term `4ⁿ/√(πn)`, uniformly in `n`.  This is
strictly sharper than the elementary sandwich `4ⁿ/(2n+1) ≤ C(2n,n) ≤ 4ⁿ`
(`ChebyshevBoundsOQ06.centralBinom_real_sandwich`), which misses the true `√(πn)`
scale entirely.

## Method

The engine is Mathlib's **effective** Stirling sequence bounds — not the mere
limit.  Writing `Sₖ = stirlingSeq k = k!/(√(2k)·(k/e)ᵏ)`, the sibling entry
`BetaDiagEffectiveRate.centralBinom_stirlingSeq` records the exact algebraic
factorization
  `C(2n,n) · √n · Sₙ²  =  S₂ₙ · 4ⁿ`.
Dividing through by `4ⁿ` and multiplying by `√(πn) = √π·√n` collapses this to the
**clean normalized ratio identity**

  **`centralBinomRatio_eq`** :  `C(2n,n)·√(πn)/4ⁿ  =  √π · S₂ₙ / Sₙ²`.

Both `Sₙ` and `S₂ₙ` are trapped in the explicit interval `[√π, e/√2]` for every
positive index, by
  * `Stirling.sqrt_pi_le_stirlingSeq`  (`√π ≤ Sₖ`, effective for all `k ≥ 1`), and
  * `Stirling.stirlingSeq'_antitone` + `Stirling.stirlingSeq_one`
    (`Sₖ ≤ S₁ = e/√2`).
Feeding these into `√π · S₂ₙ / Sₙ²` gives the two constant bounds
`2π/e² ≤ ratio ≤ e/√(2π)` (`centralBinomRatio_ge`, `centralBinomRatio_le`).

Since the ratio also tends to `1` (`centralBinomRatio_tendsto_one`, the
`Tendsto`-restatement of the parent equivalence), the constants
`2π/e² < 1 < e/√(2π)` correctly bracket the sharp asymptotic value `1`.

Everything below is derived from Mathlib's Stirling development with **0 axioms
and 0 sorries**.
-/

open Real Filter Asymptotics Stirling
open scoped Topology Nat

namespace BetaCentralBinomialAsymptoticEffectiveRate

/-- Every Stirling-sequence value at a positive index is bounded above by its
first value `stirlingSeq 1 = e/√2`, by antitonicity of `stirlingSeq ∘ succ`. -/
private lemma stirlingSeq_le_e_div_sqrt2 {m : ℕ} (hm : m ≠ 0) :
    stirlingSeq m ≤ Real.exp 1 / Real.sqrt 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have h := stirlingSeq'_antitone (Nat.zero_le k)
  simpa [Function.comp, stirlingSeq_one] using h

/-- The normalized central binomial ratio `C(2n,n)·√(πn)/4ⁿ`.  Its limit is `1`
(that is the content of the parent equivalence); this file traps it in an
explicit constant interval for every `n ≥ 1`. -/
noncomputable def centralBinomRatio (n : ℕ) : ℝ :=
  (Nat.centralBinom n : ℝ) * Real.sqrt (π * n) / 4 ^ n

/-- **Clean ratio identity.**  For `n ≥ 1`,
`C(2n,n)·√(πn)/4ⁿ = √π · stirlingSeq(2n) / stirlingSeq(n)²`.  Derived from the
sibling factorization `C(2n,n)·√n·Sₙ² = S₂ₙ·4ⁿ` by dividing by `4ⁿ` and using
`√(πn) = √π·√n`. -/
theorem centralBinomRatio_eq (n : ℕ) (hn : 1 ≤ n) :
    centralBinomRatio n
      = Real.sqrt π * stirlingSeq (2 * n) / stirlingSeq n ^ 2 := by
  have hn0 : n ≠ 0 := by omega
  have hid := BetaDiagEffectiveRate.centralBinom_stirlingSeq n hn0
  have hSpos : 0 < stirlingSeq n :=
    lt_of_lt_of_le (Real.sqrt_pos.2 Real.pi_pos) (sqrt_pi_le_stirlingSeq hn0)
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  rw [centralBinomRatio, Real.sqrt_mul Real.pi_pos.le]
  field_simp
  linear_combination hid

/-- **Effective lower bound on the ratio.**  `2π/e² ≤ C(2n,n)·√(πn)/4ⁿ` for every
`n ≥ 1`.  From `stirlingSeq(2n) ≥ √π` and `stirlingSeq(n)² ≤ (e/√2)² = e²/2`. -/
theorem centralBinomRatio_ge (n : ℕ) (hn : 1 ≤ n) :
    2 * π / Real.exp 1 ^ 2 ≤ centralBinomRatio n := by
  have hn0 : n ≠ 0 := by omega
  have h2n0 : 2 * n ≠ 0 := by omega
  have hsp : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hspos : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have hS2lo : Real.sqrt π ≤ stirlingSeq (2 * n) := sqrt_pi_le_stirlingSeq h2n0
  have hSup : stirlingSeq n ≤ Real.exp 1 / Real.sqrt 2 := stirlingSeq_le_e_div_sqrt2 hn0
  have hSpos : 0 < stirlingSeq n := lt_of_lt_of_le hspos (sqrt_pi_le_stirlingSeq hn0)
  -- stirlingSeq n ^ 2 ≤ e² / 2
  have hSsq_le : stirlingSeq n ^ 2 ≤ Real.exp 1 ^ 2 / 2 := by
    have h2 : (Real.exp 1 / Real.sqrt 2) ^ 2 = Real.exp 1 ^ 2 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    calc stirlingSeq n ^ 2 ≤ (Real.exp 1 / Real.sqrt 2) ^ 2 :=
          pow_le_pow_left₀ hSpos.le hSup 2
      _ = Real.exp 1 ^ 2 / 2 := h2
  -- (2π/e²)·(e²/2) = π
  have hconst : 2 * π / Real.exp 1 ^ 2 * (Real.exp 1 ^ 2 / 2) = π := by
    have he : (Real.exp 1 : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
  rw [centralBinomRatio_eq n hn, le_div_iff₀ (pow_pos hSpos 2)]
  calc 2 * π / Real.exp 1 ^ 2 * stirlingSeq n ^ 2
      ≤ 2 * π / Real.exp 1 ^ 2 * (Real.exp 1 ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hSsq_le (by positivity)
    _ = π := hconst
    _ = Real.sqrt π * Real.sqrt π := hsp.symm
    _ ≤ Real.sqrt π * stirlingSeq (2 * n) :=
        mul_le_mul_of_nonneg_left hS2lo hspos.le

/-- **Effective upper bound on the ratio.**  `C(2n,n)·√(πn)/4ⁿ ≤ e/√(2π)` for every
`n ≥ 1`.  From `stirlingSeq(2n) ≤ e/√2` and `stirlingSeq(n)² ≥ (√π)² = π`. -/
theorem centralBinomRatio_le (n : ℕ) (hn : 1 ≤ n) :
    centralBinomRatio n ≤ Real.exp 1 / Real.sqrt (2 * π) := by
  have hn0 : n ≠ 0 := by omega
  have h2n0 : 2 * n ≠ 0 := by omega
  have hsp : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hspos : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have hSlo : Real.sqrt π ≤ stirlingSeq n := sqrt_pi_le_stirlingSeq hn0
  have hS2up : stirlingSeq (2 * n) ≤ Real.exp 1 / Real.sqrt 2 :=
    stirlingSeq_le_e_div_sqrt2 h2n0
  have hSpos : 0 < stirlingSeq n := lt_of_lt_of_le hspos hSlo
  -- π ≤ stirlingSeq n ^ 2
  have hSsq_ge : π ≤ stirlingSeq n ^ 2 := by
    rw [← hsp, sq]
    exact mul_le_mul hSlo hSlo hspos.le (le_trans hspos.le hSlo)
  -- the constant identity √π·(e/√2) = e/√(2π)·π
  have key : Real.sqrt π * (Real.exp 1 / Real.sqrt 2)
      = Real.exp 1 / Real.sqrt (2 * π) * π := by
    have h2π : Real.sqrt (2 * π) = Real.sqrt 2 * Real.sqrt π :=
      Real.sqrt_mul (by norm_num) π
    have hb : Real.sqrt 2 ≠ 0 := by positivity
    rw [h2π]
    field_simp
    linear_combination hsp
  rw [centralBinomRatio_eq n hn, div_le_iff₀ (pow_pos hSpos 2)]
  calc Real.sqrt π * stirlingSeq (2 * n)
      ≤ Real.sqrt π * (Real.exp 1 / Real.sqrt 2) :=
        mul_le_mul_of_nonneg_left hS2up hspos.le
    _ = Real.exp 1 / Real.sqrt (2 * π) * π := key
    _ ≤ Real.exp 1 / Real.sqrt (2 * π) * stirlingSeq n ^ 2 :=
        mul_le_mul_of_nonneg_left hSsq_ge (by positivity)

/-- **Effective two-sided rate for the central binomial coefficient.**  For every
`n ≥ 1`,
`(2π/e²)·4ⁿ/√(πn) ≤ C(2n,n) ≤ (e/√(2π))·4ⁿ/√(πn)` — the explicit-constant upgrade
of the bare equivalence `C(2n,n) ~ 4ⁿ/√(πn)`. -/
theorem centralBinom_effective_rate (n : ℕ) (hn : 1 ≤ n) :
    2 * π / Real.exp 1 ^ 2 * (4 ^ n / Real.sqrt (π * n)) ≤ (Nat.centralBinom n : ℝ) ∧
    (Nat.centralBinom n : ℝ)
      ≤ Real.exp 1 / Real.sqrt (2 * π) * (4 ^ n / Real.sqrt (π * n)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (π * n) := Real.sqrt_pos.2 (mul_pos Real.pi_pos hnR)
  have hX : 0 < (4 : ℝ) ^ n / Real.sqrt (π * n) := by positivity
  -- recover C(2n,n) from the ratio
  have hexp : (Nat.centralBinom n : ℝ)
      = centralBinomRatio n * (4 ^ n / Real.sqrt (π * n)) := by
    have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
    rw [centralBinomRatio]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hexp]
    exact mul_le_mul_of_nonneg_right (centralBinomRatio_ge n hn) hX.le
  · rw [hexp]
    exact mul_le_mul_of_nonneg_right (centralBinomRatio_le n hn) hX.le

/-- **Sharpness / consistency.**  The normalized ratio tends to `1`, so the two
explicit constants `2π/e² < 1 < e/√(2π)` correctly bracket the exact leading
constant.  This is the `Tendsto`-restatement of the parent equivalence. -/
theorem centralBinomRatio_tendsto_one :
    Tendsto centralBinomRatio atTop (𝓝 1) := by
  have hbase := BetaDiagAsymptotic.centralBinom_div_stirling_tendsto_one
  refine hbase.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsn : Real.sqrt (π * n) ≠ 0 := (Real.sqrt_pos.2 (mul_pos Real.pi_pos hnR)).ne'
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  rw [centralBinomRatio, div_div_eq_mul_div]

end BetaCentralBinomialAsymptoticEffectiveRate
