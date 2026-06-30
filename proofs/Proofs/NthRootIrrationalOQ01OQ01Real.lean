/-
  Nth Root Irrationality OQ-01-OQ-01 (Real subfield): irrationality of the
  maximal-real-subfield generator `ζ + ζ⁻¹ = 2·cos(2π/n)`.

  The sibling file `NthRootIrrationalOQ01OQ01.lean` proved that a complex
  primitive `n`-th root of unity `ζ` is irrational for `n ≥ 3`, and that the
  only rational roots of unity are `±1`.

  This file pushes into the **maximal real subfield** `ℚ(ζ)⁺ = ℚ(ζ + ζ⁻¹)` of
  the cyclotomic field.  The generator `ζ + ζ⁻¹ = 2·cos(2π/n)` is the real part
  doubled; it is rational exactly when `[ℚ(ζ)⁺ : ℚ] = φ(n)/2 = 1`, i.e. when
  `φ(n) ≤ 2` (`n ∈ {1,2,3,4,6}`).  We prove the irrational direction:

      `φ(n) ≥ 3  ⟹  ζ + ζ⁻¹ ∉ ℚ`.

  This is the Niven-type statement that `2·cos(2π/n)` is irrational for
  `n ∉ {1,2,3,4,6}`.

  **Proof idea (degree argument).**  If `ζ + ζ⁻¹ = r ∈ ℚ`, then `ζ` is a root of
  the *rational* quadratic `X² − r·X + 1` (clear `ζ + ζ⁻¹ = r` by `ζ`).  Hence
  the minimal polynomial `minpoly ℚ ζ` divides a degree-2 polynomial, so
  `deg(minpoly ℚ ζ) ≤ 2`.  But `minpoly ℚ ζ = Φ_n` (Mathlib:
  `cyclotomic_eq_minpoly_rat`), whose degree is `φ(n) ≥ 3` — contradiction.

  **Key Mathlib facts used:**
  - `Polynomial.cyclotomic_eq_minpoly_rat`: `cyclotomic n ℚ = minpoly ℚ ζ`.
  - `Polynomial.natDegree_cyclotomic`: `deg Φ_n = φ(n)`.
  - `minpoly.dvd` + `Polynomial.natDegree_le_of_dvd`: degree bound from a root.

  **Results (0 axioms, 0 sorries):**
  1. `trace_not_rational`       : `φ(n) ≥ 3 → ζ + ζ⁻¹ ∉ range(ℚ → ℂ)`.
  2. `fifthRoot_trace_not_rational` : concrete instance `n = 5`
       (`2·cos(2π/5) = (√5 − 1)/2` is irrational).

  ## References
  - Niven, I. (1956). "Irrational Numbers." Carus Math. Monographs, Thm 3.9.
  - Washington, L. (1997). "Introduction to Cyclotomic Fields." §2 (real subfield).
-/

import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open Polynomial

namespace NthRootIrrationalOQ01OQ01Real

noncomputable section

-- ============================================================================
-- Main theorem: the cyclotomic "trace" ζ + ζ⁻¹ is irrational when φ(n) ≥ 3
-- ============================================================================

/-- **Irrationality of the real cyclotomic generator.**  If `ζ : ℂ` is a
    primitive `n`-th root of unity with `φ(n) ≥ 3`, then `ζ + ζ⁻¹` (which equals
    `2·cos(2π/n)`) is not the image of any rational number; i.e. it is
    irrational.

    The bound `φ(n) ≥ 3` is sharp: `φ(n) ≤ 2` exactly for `n ∈ {1,2,3,4,6}`,
    where `2·cos(2π/n) ∈ {2, −2, −1, 0, 1}` is rational. -/
theorem trace_not_rational {n : ℕ} (hn : 3 ≤ n.totient) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) :
    ζ + ζ⁻¹ ∉ Set.range ((algebraMap ℚ ℂ) : ℚ → ℂ) := by
  rintro ⟨r, hr⟩
  -- `n > 0` from `φ(n) ≥ 3 > 0`.
  have hnpos : 0 < n := Nat.totient_pos.mp (by omega)
  -- `ζ ≠ 0` (a primitive root of unity is a unit).
  have hζ0 : ζ ≠ 0 := by
    intro h
    have hpow : ζ ^ n = 1 := hζ.pow_eq_one
    rw [h, zero_pow hnpos.ne'] at hpow
    exact one_ne_zero hpow.symm
  -- `ζ` is a root of the rational quadratic `q = X² − r·X + 1`.
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
  -- The minimal polynomial divides `q`, so its degree is ≤ 2.
  have hdvd : minpoly ℚ ζ ∣ q := minpoly.dvd ℚ ζ haeval
  have hle : (minpoly ℚ ζ).natDegree ≤ q.natDegree := natDegree_le_of_dvd hdvd hqne
  -- But `minpoly ℚ ζ = Φ_n`, of degree `φ(n) ≥ 3`.
  have hcyc : cyclotomic n ℚ = minpoly ℚ ζ := cyclotomic_eq_minpoly_rat hζ hnpos
  have hmindeg : (minpoly ℚ ζ).natDegree = n.totient := by
    rw [← hcyc, natDegree_cyclotomic]
  rw [hmindeg, hqdeg] at hle
  omega

-- ============================================================================
-- Concrete instance: 2·cos(2π/5) = (√5 − 1)/2 is irrational
-- ============================================================================

/-- The real cyclotomic generator for `n = 5`, namely
    `e^{2πi/5} + e^{-2πi/5} = 2·cos(2π/5) = (√5 − 1)/2`, is irrational.
    Here `φ(5) = 4 ≥ 3`. -/
theorem fifthRoot_trace_not_rational :
    Complex.exp (2 * ↑Real.pi * Complex.I / (5 : ℕ)) +
        (Complex.exp (2 * ↑Real.pi * Complex.I / (5 : ℕ)))⁻¹ ∉
      Set.range ((algebraMap ℚ ℂ) : ℚ → ℂ) :=
  trace_not_rational (n := 5) (by decide)
    (Complex.isPrimitiveRoot_exp 5 (by norm_num))

end

end NthRootIrrationalOQ01OQ01Real
