/-
  Nth Root Irrationality OQ-01-OQ-01 (Niven, real cosine):
  irrationality of `cos(2π/n)` **as a real number**.

  The sibling files prove:
  * `NthRootIrrationalOQ01OQ01.lean` — a complex primitive `n`-th root of unity
    `ζ` is irrational for `n ≥ 3`, and the only rational roots of unity are `±1`.
  * `NthRootIrrationalOQ01OQ01Real.lean` — the *abstract* generator
    `ζ + ζ⁻¹` of the maximal real subfield `ℚ(ζ)⁺` is irrational when
    `φ(n) ≥ 3` (i.e. `ζ + ζ⁻¹ ∉ range(ℚ → ℂ)`).

  That last statement is phrased in terms of the abstract complex quantity
  `ζ + ζ⁻¹`; it never connects to the genuine real analytic function
  `Real.cos`.  **This file closes that last mile.**  Using
  `ζ + ζ⁻¹ = 2·cos(2π/n)` (via `Complex.exp_mul_I`) it proves the textbook
  Niven statement:

      `φ(n) ≥ 3  ⟹  Irrational (Real.cos (2π/n))`.

  The bound `φ(n) ≥ 3` (⇔ `n ∉ {1,2,3,4,6}`) is sharp: for `n ∈ {1,2,3,4,6}`
  one has `cos(2π/n) ∈ {1, −1, −1/2, 0, 1/2}`, all rational.

  **Proof outline.**
  1. `trace_not_rational` (re-proved inline, identifiers name-checked against
     `leanprover-community/mathlib4` master): if `φ(n) ≥ 3` and `ζ` is a
     primitive `n`-th root of unity, then `ζ + ζ⁻¹ ∉ range(algebraMap ℚ ℂ)`.
     [degree argument: a rational `ζ + ζ⁻¹` makes `ζ` a root of the rational
     quadratic `X² − rX + 1`, forcing `deg(minpoly ℚ ζ) = φ(n) ≤ 2`.]
  2. `exp_add_inv_eq_two_cos`: `exp(θi) + exp(θi)⁻¹ = 2·cos θ` for real `θ`.
  3. Specialise to `ζ = exp(2πi/n)` (Mathlib `Complex.isPrimitiveRoot_exp`),
     so `ζ + ζ⁻¹ = 2·cos(2π/n)`.  A rational `cos(2π/n)` would put `ζ + ζ⁻¹`
     in `range(algebraMap ℚ ℂ)`, contradicting (1).

  **Key Mathlib facts used:**
  - `Complex.isPrimitiveRoot_exp`, `Complex.exp_mul_I`, `Complex.exp_neg`,
    `Complex.cos_neg`, `Complex.sin_neg`, `Complex.ofReal_cos`.
  - `Polynomial.cyclotomic_eq_minpoly_rat`, `Polynomial.natDegree_cyclotomic`,
    `minpoly.dvd`, `Polynomial.natDegree_le_of_dvd`.

  **Results (0 axioms, 0 sorries):**
  1. `trace_not_rational`             : `φ(n) ≥ 3 → ζ + ζ⁻¹ ∉ range(ℚ → ℂ)`.
  2. `exp_add_inv_eq_two_cos`         : `exp(θi) + exp(θi)⁻¹ = 2·cos θ`.
  3. `cos_two_pi_div_n_irrational`    : `φ(n) ≥ 3 → Irrational (cos(2π/n))`.
  4. `cos_two_pi_div_five_irrational` : concrete `n = 5`.

  ## References
  - Niven, I. (1956). "Irrational Numbers." Carus Math. Monographs, Thm 3.9.
  - Washington, L. (1997). "Introduction to Cyclotomic Fields." §2.
-/

import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open Polynomial

namespace NthRootIrrationalOQ01OQ01Cos

noncomputable section

-- ============================================================================
-- Step 1: the abstract real-subfield generator `ζ + ζ⁻¹` is irrational
--          (re-proved inline so this file is self-contained)
-- ============================================================================

/-- If `ζ : ℂ` is a primitive `n`-th root of unity with `φ(n) ≥ 3`, then
    `ζ + ζ⁻¹` is not the image of any rational number. -/
theorem trace_not_rational {n : ℕ} (hn : 3 ≤ n.totient) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) :
    ζ + ζ⁻¹ ∉ Set.range ((algebraMap ℚ ℂ) : ℚ → ℂ) := by
  rintro ⟨r, hr⟩
  have hnpos : 0 < n := Nat.totient_pos.mp (by omega)
  have hζ0 : ζ ≠ 0 := by
    intro h
    have hpow : ζ ^ n = 1 := hζ.pow_eq_one
    rw [h, zero_pow hnpos.ne'] at hpow
    exact one_ne_zero hpow.symm
  set q : ℚ[X] := X ^ 2 - C r * X + 1 with hq
  have haeval : (aeval ζ) q = 0 := by
    have hmul : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
    rw [hq]
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_one]
    rw [hr]
    linear_combination -hmul
  have hqdeg : q.natDegree = 2 := by rw [hq]; compute_degree!
  have hqne : q ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hqdeg
    omega
  have hdvd : minpoly ℚ ζ ∣ q := minpoly.dvd ℚ ζ haeval
  have hle : (minpoly ℚ ζ).natDegree ≤ q.natDegree := natDegree_le_of_dvd hdvd hqne
  have hcyc : cyclotomic n ℚ = minpoly ℚ ζ := cyclotomic_eq_minpoly_rat hζ hnpos
  have hmindeg : (minpoly ℚ ζ).natDegree = n.totient := by
    rw [← hcyc, natDegree_cyclotomic]
  rw [hmindeg, hqdeg] at hle
  omega

-- ============================================================================
-- Step 2: the Euler bridge `exp(θi) + exp(θi)⁻¹ = 2·cos θ`
-- ============================================================================

/-- For real `θ`, `exp(θi) + exp(θi)⁻¹ = 2·cos θ` (a complexification of the
    real cosine).  This is the identity `ζ + ζ⁻¹ = 2·cos(2π/n)` once `ζ` is the
    standard exponential primitive root. -/
private lemma exp_add_inv_eq_two_cos (θ : ℝ) :
    Complex.exp (↑θ * Complex.I) + (Complex.exp (↑θ * Complex.I))⁻¹
      = 2 * ((Real.cos θ : ℝ) : ℂ) := by
  have h1 : (Complex.exp (↑θ * Complex.I))⁻¹ = Complex.exp ((-↑θ) * Complex.I) := by
    rw [← Complex.exp_neg, neg_mul]
  rw [h1, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_cos]
  ring

-- ============================================================================
-- Step 3: Niven's theorem — `cos(2π/n)` is irrational when `φ(n) ≥ 3`
-- ============================================================================

/-- **Niven's theorem (real cosine form).**  If `φ(n) ≥ 3` then
    `cos(2π/n)` is irrational.  Sharp: `φ(n) ≤ 2` (`n ∈ {1,2,3,4,6}`) is exactly
    where `cos(2π/n) ∈ {1, −1, −1/2, 0, 1/2}` is rational. -/
theorem cos_two_pi_div_n_irrational {n : ℕ} (hn : 3 ≤ n.totient) :
    Irrational (Real.cos (2 * Real.pi / n)) := by
  have hn0 : n ≠ 0 := by
    have : 0 < n := Nat.totient_pos.mp (by omega)
    omega
  set ζ : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑n) with hζdef
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have harg : (2 * ↑Real.pi * Complex.I / ↑n : ℂ)
      = (↑(2 * Real.pi / (n : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  have hsum : ζ + ζ⁻¹ = 2 * ((Real.cos (2 * Real.pi / (n : ℝ)) : ℝ) : ℂ) := by
    rw [hζdef, harg, exp_add_inv_eq_two_cos]
  intro hmem
  obtain ⟨c, hc⟩ := hmem
  apply trace_not_rational hn hζ
  refine ⟨2 * c, ?_⟩
  rw [hsum, ← hc, eq_ratCast]
  push_cast
  ring

/-- Concrete instance: `cos(2π/5)` is irrational (here `φ(5) = 4 ≥ 3`).
    Numerically `cos(2π/5) = (√5 − 1)/4`. -/
theorem cos_two_pi_div_five_irrational :
    Irrational (Real.cos (2 * Real.pi / (5 : ℕ))) :=
  cos_two_pi_div_n_irrational (n := 5) (by decide)

end

end NthRootIrrationalOQ01OQ01Cos
