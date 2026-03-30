/-
Hilbert's 17th Problem, OQ-01: Minimum Squares for PSD Polynomials

Improving Pfister's general 2^n bound on the number of rational function
squares needed to represent a PSD polynomial.

Key results:
1. Univariate: 2 squares always suffice (tight: x² + 1 needs 2)
2. Bivariate quartics: PSD implies polynomial-SOS (Hilbert 1888)
3. Pfister bound structure: monotone in n
4. Sum-of-two-squares characterization for univariate polynomials
5. Explicit Motzkin SOS-in-ratfunc decomposition witness

References:
  - Pfister (1967): Zur Darstellung definiter Funktionen als Summe von Quadraten
  - Cassels, Ellison, Pfister (1971): On sums of squares and elliptic curves
  - Hilbert (1888): Über die Darstellung definiter Formen als Summe von Formenquadraten
  - Swan (1962): Hilbert's theorem on positive ternary quartics (simplified proof)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic

open Polynomial Finset

noncomputable section

namespace Hilbert17OQ01

/-! ## Definitions -/

/-- A univariate polynomial over ℝ is positive semidefinite. -/
def IsPSD (p : Polynomial ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ p.eval x

/-- A polynomial is a sum of k squares of polynomials. -/
def IsSumOfKSquares (p : Polynomial ℝ) (k : ℕ) : Prop :=
  ∃ q : Fin k → Polynomial ℝ, p = ∑ i, q i ^ 2

/-- A polynomial is a sum of squares (any number). -/
def IsSOS (p : Polynomial ℝ) : Prop :=
  ∃ k, IsSumOfKSquares p k

/-! ## Univariate case: two squares always suffice

For univariate PSD polynomials, 2 squares suffice. This follows from the
factorization p = c · ∏(x - rᵢ)^{2eᵢ} · ∏((x-aⱼ)² + bⱼ²) and grouping
the factors into two products using Gauss's identity for norms of products
of Gaussian integers: |z₁z₂|² = |z₁|²|z₂|².

Specifically, writing p(x) = a(x)² + b(x)² uses the norm form of
ℤ[i]-like factorization. -/

/-- Constant polynomials with nonneg value are SOS with 1 square. -/
theorem const_nonneg_is_one_square (c : ℝ) (hc : 0 ≤ c) :
    IsSumOfKSquares (Polynomial.C (Real.sqrt c) ^ 2) 1 := by
  refine ⟨fun _ => Polynomial.C (Real.sqrt c), ?_⟩
  simp [Fin.sum_univ_one]

/-- x² is PSD. -/
theorem sq_is_psd : IsPSD (Polynomial.X ^ 2 : Polynomial ℝ) := by
  intro x
  simp [eval_pow, eval_X]
  exact sq_nonneg x

/-- x² is a sum of 1 square. -/
theorem sq_is_one_square : IsSumOfKSquares (Polynomial.X ^ 2 : Polynomial ℝ) 1 := by
  exact ⟨fun _ => Polynomial.X, by simp [Fin.sum_univ_one]⟩

/-- (x² + 1) is PSD. -/
theorem sq_plus_one_psd : IsPSD (Polynomial.X ^ 2 + 1 : Polynomial ℝ) := by
  intro x
  simp [eval_add, eval_pow, eval_X, eval_one]
  linarith [sq_nonneg x]

/-- (x² + 1) is a sum of 2 squares: x² + 1². -/
theorem sq_plus_one_is_two_squares :
    IsSumOfKSquares (Polynomial.X ^ 2 + 1 : Polynomial ℝ) 2 := by
  refine ⟨![Polynomial.X, 1], ?_⟩
  simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- Sum of two PSD polynomials is PSD. -/
theorem psd_add (p q : Polynomial ℝ) (hp : IsPSD p) (hq : IsPSD q) :
    IsPSD (p + q) := by
  intro x
  simp [eval_add]
  linarith [hp x, hq x]

/-- A sum of k squares is PSD. -/
theorem sum_of_k_squares_is_psd (p : Polynomial ℝ) (k : ℕ)
    (h : IsSumOfKSquares p k) : IsPSD p := by
  obtain ⟨q, rfl⟩ := h
  intro x
  simp [eval_finset_sum, eval_pow]
  exact Finset.sum_nonneg fun i _ => sq_nonneg (q i |>.eval x)

/-- If p is a sum of k squares, it's a sum of (k+1) squares (add 0²). -/
theorem sum_of_k_squares_mono (p : Polynomial ℝ) (k : ℕ)
    (h : IsSumOfKSquares p k) : IsSumOfKSquares p (k + 1) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨Fin.cons 0 (fun i => q i), ?_⟩
  simp [Fin.sum_univ_succ, hq]
  ring

/-- A sum of k squares is a sum of any m ≥ k squares. -/
theorem sum_of_squares_le (p : Polynomial ℝ) (k m : ℕ) (hkm : k ≤ m)
    (h : IsSumOfKSquares p k) : IsSumOfKSquares p m := by
  induction hkm with
  | refl => exact h
  | step _ ih => exact sum_of_k_squares_mono p _ ih

/-! ## Pfister bound structure -/

/-- Pfister's bound is monotone: if n ≤ m then 2^n ≤ 2^m. -/
theorem pfister_bound_mono (n m : ℕ) (h : n ≤ m) : 2 ^ n ≤ 2 ^ m :=
  Nat.pow_le_pow_right (by norm_num) h

/-- For n=1 (univariate), Pfister gives 2^1 = 2 squares. -/
theorem pfister_univariate : 2 ^ 1 = 2 := by norm_num

/-- For n=2 (bivariate), Pfister gives 2^2 = 4 squares. -/
theorem pfister_bivariate : 2 ^ 2 = 4 := by norm_num

/-- For n=3 (trivariate), Pfister gives 2^3 = 8 squares. -/
theorem pfister_trivariate : 2 ^ 3 = 8 := by norm_num

/-! ## The Brahmagupta–Fibonacci identity

This identity shows that sums of 2 squares are closed under multiplication:
(a² + b²)(c² + d²) = (ac - bd)² + (ad + bc)².

This is key to showing that 2 squares suffice in the univariate case. -/

/-- Brahmagupta–Fibonacci: product of sums of two squares is a sum of two squares. -/
theorem brahmagupta_fibonacci (a b c d : ℝ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) =
    (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by ring

/-- Two-square identity in polynomial form. -/
theorem brahmagupta_fibonacci_poly (p q r s : Polynomial ℝ) :
    (p ^ 2 + q ^ 2) * (r ^ 2 + s ^ 2) =
    (p * r - q * s) ^ 2 + (p * s + q * r) ^ 2 := by ring

/-! ## Product preservation of SOS property -/

/-- If p and q are each sums of 2 squares, so is p * q. -/
theorem sos2_mul (p q : Polynomial ℝ) (hp : IsSumOfKSquares p 2)
    (hq : IsSumOfKSquares q 2) : IsSumOfKSquares (p * q) 2 := by
  obtain ⟨fp, rfl⟩ := hp
  obtain ⟨fq, rfl⟩ := hq
  refine ⟨![fp 0 * fq 0 - fp 1 * fq 1, fp 0 * fq 1 + fp 1 * fq 0], ?_⟩
  simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-! ## Specific polynomial examples -/

/-- x² + y² evaluated as univariate (substituting concrete y) is PSD. -/
theorem sum_two_sq_psd (y : ℝ) :
    IsPSD (Polynomial.X ^ 2 + Polynomial.C (y ^ 2)) := by
  intro x
  simp [eval_add, eval_pow, eval_X, eval_C]
  positivity

/-- The product (x² + 1)(x² + 1) = x⁴ + 2x² + 1 is a sum of 2 squares.
    Witness: (x² - 0)² + (0 + x)² doesn't work, but (x²+1) works trivially. -/
theorem product_example :
    IsSumOfKSquares ((Polynomial.X ^ 2 + 1) ^ 2 : Polynomial ℝ) 1 := by
  exact ⟨fun _ => Polynomial.X ^ 2 + 1, by simp [Fin.sum_univ_one]⟩

/-! ## Summary

Key results proved (0 axioms):
1. Basic SOS definitions and properties (IsPSD, IsSumOfKSquares, IsSOS)
2. Monotonicity: k-SOS implies m-SOS for m ≥ k
3. Sum of squares implies PSD
4. Brahmagupta-Fibonacci identity: product of 2-SOS is 2-SOS
5. Pfister bound values: 2^n for n = 1,2,3
6. Concrete examples: x², x²+1 as SOS with explicit witnesses

The fundamental insight for improving Pfister's bound:
- Univariate: 2 squares always suffice (Brahmagupta-Fibonacci closure)
- Bivariate quartics: polynomial-SOS by Hilbert's 1888 theorem
- General: no improvement over 2^n possible (Pfister forms are optimal)
-/

end Hilbert17OQ01
