/-
# De Moivre's Theorem and the Sum of the Roots of Unity (OQ-03)

## Research Question

The parent entry (`EulerIdentityOQ01`, "Euler's Formula via Taylor Series
Splitting") formalizes Euler's formula `e^{ix} = cos x + i·sin x`. The natural
*multiplicative* consequence of Euler's formula is **De Moivre's theorem**

    (cos x + i·sin x)^n = cos(nx) + i·sin(nx),

which Mathlib does **not** expose as a named lemma: it has `Complex.exp_nat_mul`
and `Complex.exp_int_mul`, but no `cos + i sin` power law, and no statement that
the `n`-th roots of unity sum to zero phrased through Euler's formula. Can De
Moivre's theorem — and that structural consequence — be derived directly from
Euler's formula?

## Answer

Yes. Writing `cos x + i·sin x = e^{ix}` (Euler) collapses the power on the left
to `(e^{ix})^n = e^{inx}` (`Complex.exp_nat_mul`), and a second application of
Euler re-expands `e^{inx} = cos(nx) + i·sin(nx)`. The same argument with
`exp_int_mul` gives the integer (hence negative-exponent) form.

For the roots of unity we set `ω_n = e^{2πi/n} = cos(2π/n) + i·sin(2π/n)`. Then
`ω_n^n = e^{2πi} = 1` (so it is an `n`-th root of unity), `ω_n ≠ 1` for `n ≥ 2`
(via `Complex.exp_eq_one_iff`), and the finite geometric series gives
`∑_{k<n} ω_n^k = (ω_n^n − 1)/(ω_n − 1) = 0`. Thus the `n`-th roots of unity sum
to zero — the classical "centre of mass of a regular polygon is its centre".

## Relation to the parent

The parent derives Euler's formula `e^{ix} = cos x + i·sin x` from the Taylor
series with 0 axioms. Here we take Euler's formula as established (re-proving it
in one line from Mathlib's `Complex.exp_mul_I`, the canonical statement the
parent reconstructs) and build the multiplicative theory on top of it.

NOTE: the parent file `Proofs/EulerIdentityOQ01.lean` does not currently compile
under Mathlib v4.26.0 (its local lemmas `cos_eq_tsum`/`sin_eq_tsum` now collide
by name with Mathlib's, producing "Ambiguous term" errors), so this file is kept
self-contained rather than importing it.

## Axiom Budget

0 axioms. Everything is standard Mathlib (`exp_mul_I`, `exp_nat_mul`,
`exp_int_mul`, `exp_two_pi_mul_I`, `exp_eq_one_iff`, `geom_sum_eq`).

Source: Extension of `EulerIdentityOQ01` (OQ-03).
-/

import Mathlib

open Complex
open scoped Real
open Finset

namespace EulerIdentityOQ01OQ03

-- ============================================================================
-- § 0. EULER'S FORMULA (real argument)
-- ============================================================================

/-- **Euler's formula** for a real angle, `e^{ix} = cos x + i·sin x`.

    This is Mathlib's `Complex.exp_mul_I` specialised to a real angle, with the
    complex `cos`/`sin` pushed back to real `cos`/`sin`. It is the same statement
    the parent entry reconstructs from the Taylor series. -/
theorem euler_formula (x : ℝ) :
    Complex.exp ((x : ℂ) * I) = ↑(Real.cos x) + ↑(Real.sin x) * I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

-- ============================================================================
-- § 1. DE MOIVRE'S THEOREM
-- ============================================================================

/-- **De Moivre's Theorem** (natural exponent).

    `(cos x + i·sin x)^n = cos(nx) + i·sin(nx)`.

    Proof: rewrite `cos x + i·sin x = e^{ix}` (Euler), collapse the power via
    `e^{inx} = (e^{ix})^n`, then re-expand with Euler at `nx`. -/
theorem de_moivre (x : ℝ) (n : ℕ) :
    (↑(Real.cos x) + ↑(Real.sin x) * I) ^ n
      = ↑(Real.cos ((n : ℝ) * x)) + ↑(Real.sin ((n : ℝ) * x)) * I := by
  rw [← euler_formula x, ← Complex.exp_nat_mul]
  rw [show (n : ℂ) * ((x : ℂ) * I) = (((n : ℝ) * x : ℝ) : ℂ) * I from by
    push_cast; ring]
  rw [euler_formula]

/-- **De Moivre's Theorem** (integer exponent).

    `(cos x + i·sin x)^n = cos(nx) + i·sin(nx)` for all `n : ℤ`.

    This covers negative powers, e.g. `(cos x + i·sin x)⁻¹ = cos x − i·sin x`. -/
theorem de_moivre_int (x : ℝ) (n : ℤ) :
    (↑(Real.cos x) + ↑(Real.sin x) * I) ^ n
      = ↑(Real.cos ((n : ℝ) * x)) + ↑(Real.sin ((n : ℝ) * x)) * I := by
  rw [← euler_formula x, ← Complex.exp_int_mul]
  rw [show (n : ℂ) * ((x : ℂ) * I) = (((n : ℝ) * x : ℝ) : ℂ) * I from by
    push_cast; ring]
  rw [euler_formula]

-- ============================================================================
-- § 2. THE PRINCIPAL n-TH ROOT OF UNITY
-- ============================================================================

/-- The principal `n`-th root of unity `ω_n = e^{2πi/n}`. -/
noncomputable def rou (n : ℕ) : ℂ := Complex.exp (((2 * π / n : ℝ)) * I)

/-- `ω_n = cos(2π/n) + i·sin(2π/n)` — the geometric description via Euler. -/
theorem rou_eq_cos_add_sin (n : ℕ) :
    rou n = ↑(Real.cos (2 * π / n)) + ↑(Real.sin (2 * π / n)) * I := by
  rw [rou, euler_formula]

/-- `ω_n` is genuinely an `n`-th root of unity: `ω_n^n = 1`.

    By De Moivre, `ω_n^n = cos(n·(2π/n)) + i·sin(n·(2π/n)) = cos(2π) + i·sin(2π)
    = 1`. -/
theorem rou_pow_n (n : ℕ) (hn : n ≠ 0) : (rou n) ^ n = 1 := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [rou_eq_cos_add_sin, de_moivre, show (n : ℝ) * (2 * π / n) = 2 * π from by
    field_simp, Real.cos_two_pi, Real.sin_two_pi]
  push_cast; ring

/-- For `n ≥ 2`, the principal root is not `1`. -/
theorem rou_ne_one (n : ℕ) (hn : 2 ≤ n) : rou n ≠ 1 := by
  intro hcontra
  simp only [rou, Complex.exp_eq_one_iff] at hcontra
  obtain ⟨k, hk⟩ := hcontra
  -- hk : (↑(2 * π / ↑n)) * I = ↑k * (2 * π * I)
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  -- Cancel the common factor `I` to reduce to a real-coefficient identity.
  have hk2 : ((2 * π / n : ℝ) : ℂ) = (k : ℂ) * (2 * π) := by
    have h : ((2 * π / n : ℝ) : ℂ) * I = ((k : ℂ) * (2 * π)) * I := by
      rw [hk]; ring
    exact mul_right_cancel₀ hI h
  -- Take real parts: `2π/n = k·2π`.
  have hreal : (2 * π / n : ℝ) = (k : ℝ) * (2 * π) := by
    have hre := congrArg Complex.re hk2
    push_cast at hre
    simpa using hre
  -- π > 0 and n ≥ 2 squeeze `k` strictly between 0 and 1, impossible for `k : ℤ`.
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hnpos : (0 : ℝ) < n := by positivity
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlow : (0 : ℝ) < (k : ℝ) * (2 * π) := by rw [← hreal]; positivity
  have hk_pos : (0 : ℝ) < (k : ℝ) := by nlinarith [hlow, h2pi]
  have hupp : (2 * π / n : ℝ) < 2 * π := by
    rw [div_lt_iff₀ hnpos]; nlinarith [hpi, hnreal]
  have hk_lt : (k : ℝ) * (2 * π) < 2 * π := by rw [← hreal]; exact hupp
  have hk_lt1 : (k : ℝ) < 1 := by nlinarith [hk_lt, h2pi]
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hk_pos
  have hk1 : k < 1 := by exact_mod_cast hk_lt1
  omega

-- ============================================================================
-- § 3. SUM OF THE n-TH ROOTS OF UNITY
-- ============================================================================

/-- **The `n`-th roots of unity sum to zero** (for `n ≥ 2`):

    `∑_{k=0}^{n-1} ω_n^k = 0`.

    The points `ω_n^k = e^{2πik/n}` are the vertices of a regular `n`-gon
    inscribed in the unit circle; their centroid is the origin. The proof is the
    finite geometric series `(ω_n^n − 1)/(ω_n − 1) = 0`, using `ω_n^n = 1` and
    `ω_n ≠ 1`. -/
theorem sum_rou_pow_eq_zero (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ range n, (rou n) ^ k = 0 := by
  have hne : rou n ≠ 1 := rou_ne_one n hn
  rw [geom_sum_eq hne, rou_pow_n n (by omega), sub_self, zero_div]

end EulerIdentityOQ01OQ03
