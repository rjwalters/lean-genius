/-
# Euler Identity: Axiom Elimination (OQ-01-OQ-01)

## Open Question: euler-identity-oq-01-oq-01

EulerIdentityOQ01.lean proved Euler's identity using 3 axioms:
- `tsum_even_add_odd`: splitting ∑' aₙ into even/odd parts
- `cos_eq_tsum`: cos x = ∑' k, evenTerm x k
- `sin_eq_tsum`: sin x * I = ∑' k, oddTerm x k

This file proves all three as theorems from Mathlib, giving a fully axiom-free,
sorry-free formalization.

## Proof Strategy

1. **tsum_even_add_odd**: `Summable.comp_injective` derives summability of even/odd
   subseries (maps 2*· and 2*·+1 are injective), then Mathlib's `tsum_even_add_odd`.

2. **cos_eq_tsum**: `Complex.cos_eq_tsum` + `ofReal_cos` (lift from ℝ to ℂ).

3. **sin_eq_tsum**: `Complex.sin_eq_tsum` + `← tsum_mul_right`.

4. **euler_formula** and **euler_identity** follow as corollaries (using `Complex.exp_mul_I`
   to avoid an unresolved API gap between `Complex.exp` and `NormedSpace.exp`).
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

open Complex Real
open scoped Nat

namespace EulerIdentityOQ01OQ01

/-! ## Power Series Terms -/

/-- The general term of the exponential series: z^n / n! -/
noncomputable def expTerm (z : ℂ) (n : ℕ) : ℂ := z ^ n / n.factorial

/-- The even-index term: (ix)^{2k}/(2k)! = (-1)^k x^{2k}/(2k)! -/
noncomputable def evenTerm (x : ℝ) (k : ℕ) : ℂ :=
  ((-1 : ℂ) ^ k * (x : ℂ) ^ (2 * k)) / (2 * k).factorial

/-- The odd-index term: (ix)^{2k+1}/(2k+1)! = i·(-1)^k x^{2k+1}/(2k+1)! -/
noncomputable def oddTerm (x : ℝ) (k : ℕ) : ℂ :=
  (I * (-1 : ℂ) ^ k * (x : ℂ) ^ (2 * k + 1)) / (2 * k + 1).factorial

/-! ## Algebraic Identities: Powers of i -/

private theorem I_pow_even (k : ℕ) : (I : ℂ) ^ (2 * k) = (-1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 from by ring, pow_add, ih, I_sq]; ring

private theorem I_pow_odd (k : ℕ) : (I : ℂ) ^ (2 * k + 1) = I * (-1) ^ k := by
  rw [pow_succ, I_pow_even]; ring

/-- The even-indexed exp term equals the cosine series term. -/
theorem expTerm_even (x : ℝ) (k : ℕ) :
    expTerm (↑x * I) (2 * k) = evenTerm x k := by
  simp only [expTerm, evenTerm]
  rw [mul_pow, show (↑x : ℂ) ^ (2 * k) * I ^ (2 * k) = I ^ (2 * k) * (↑x) ^ (2 * k) from
    by ring, I_pow_even]

/-- The odd-indexed exp term equals the sine series term (times i). -/
theorem expTerm_odd (x : ℝ) (k : ℕ) :
    expTerm (↑x * I) (2 * k + 1) = oddTerm x k := by
  simp only [expTerm, oddTerm]
  rw [mul_pow, show (↑x : ℂ) ^ (2 * k + 1) * I ^ (2 * k + 1) =
    I ^ (2 * k + 1) * (↑x) ^ (2 * k + 1) from by ring, I_pow_odd]

/-- Summability of the exponential series. -/
theorem expSeries_summable (z : ℂ) : Summable (expTerm z) := by
  have h := NormedSpace.expSeries_summable (𝕂 := ℂ) z
  exact h.congr fun n => by
    simp [expTerm, NormedSpace.expSeries, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-! ## Step 1: tsum_even_add_odd as a theorem -/

/-- **tsum_even_add_odd** (formerly an axiom in EulerIdentityOQ01).

Uses `Summable.comp_injective`: the maps (2*·) and (2*·+1) are injective, so
summability of the full series implies summability of each subseries. Then
Mathlib's `tsum_even_add_odd` gives the splitting. -/
theorem tsum_even_add_odd_of_summable {a : ℕ → ℂ} (ha : Summable a) :
    ∑' n, a n = (∑' k, a (2 * k)) + (∑' k, a (2 * k + 1)) := by
  have he : Summable (fun k => a (2 * k)) :=
    ha.comp_injective (fun i j h => by omega)
  have ho : Summable (fun k => a (2 * k + 1)) :=
    ha.comp_injective (fun i j h => by omega)
  exact (tsum_even_add_odd he ho).symm

/-! ## Step 2: cos_eq_tsum as a theorem -/

/-- **cos_eq_tsum** (formerly an axiom in EulerIdentityOQ01).

↑(cos x) = ∑' k, (-1)^k x^{2k}/(2k)!, using `Complex.cos_eq_tsum` and `ofReal_cos`. -/
theorem cos_eq_tsum_thm (x : ℝ) :
    (↑(Real.cos x) : ℂ) = ∑' k, evenTerm x k := by
  rw [ofReal_cos, Complex.cos_eq_tsum]
  apply tsum_congr; intro k
  simp only [evenTerm]

/-! ## Step 3: sin_eq_tsum as a theorem -/

/-- **sin_eq_tsum** (formerly an axiom in EulerIdentityOQ01).

↑(sin x) * I = ∑' k, oddTerm x k, using `Complex.sin_eq_tsum` and `← tsum_mul_right`. -/
theorem sin_eq_tsum_thm (x : ℝ) :
    (↑(Real.sin x) : ℂ) * I = ∑' k, oddTerm x k := by
  rw [ofReal_sin, Complex.sin_eq_tsum]
  rw [← tsum_mul_right]
  apply tsum_congr; intro k
  simp only [oddTerm]
  ring

/-! ## Corollary: Axiom-Free Euler's Formula and Identity -/

/-- **Euler's formula**, proved without any axioms or sorries.

The three lemmas above (tsum_even_add_odd_of_summable, cos_eq_tsum_thm, sin_eq_tsum_thm)
eliminate all axioms from EulerIdentityOQ01. The formula itself follows from Mathlib's
`Complex.exp_mul_I`. -/
theorem euler_formula (x : ℝ) :
    exp (↑x * I) = ↑(Real.cos x) + ↑(Real.sin x) * I := by
  rw [ofReal_cos, ofReal_sin]
  exact Complex.exp_mul_I x

/-- **Euler's identity** e^(iπ) + 1 = 0. -/
theorem euler_identity : exp (↑π * I) + 1 = 0 := by
  have h : exp (↑π * I) = -1 := by
    rw [euler_formula, Real.cos_pi, Real.sin_pi]
    push_cast; ring
  rw [h]; ring

end EulerIdentityOQ01OQ01
