import Mathlib

/-!
# Cayley-Hamilton OQ-02-OQ-04: Closed-form powers of a 2×2 matrix

The parent entry (`cayley-hamilton-oq-02`) gives the *abstract* reduction
`Aᵏ = (Xᵏ mod χ_A)(A)`: every power of a matrix is a polynomial of degree `< n`
in the matrix, but it leaves the reduced polynomial implicit.  This entry makes the
reduction **explicit** in the smallest interesting case, `n = 2`, where the
characteristic polynomial has degree two and the recursion closes into a single
**Lucas (binary linear) sequence**.

## The closed form

For a `2 × 2` matrix `M` over a commutative ring `R`, write `t = tr M` and
`d = det M`.  The Cayley–Hamilton theorem specialises to
`M² = t • M − d • 1`.  Define the **Lucas sequence of the first kind** attached to
the characteristic polynomial `X² − tX + d`:

* `u 0 = 0`, `u 1 = 1`, `u (k+2) = t · u (k+1) − d · u k`.

Then every power of `M` is an *explicit* affine combination of `M` and the
identity:

$$ M^{\,n+1} \;=\; u_{n+1}\,M \;-\; d\,u_{n}\,\mathbf 1. $$

This is the content of `pow_succ_eq_lucasU_smul` below.  It is fully general:
**any** `2 × 2` matrix over **any** commutative (nontrivial) ring, no
diagonalisability, no eigenvalue hypotheses — the closed form is a direct
consequence of Cayley–Hamilton and a one-line induction.

## Showcase: the Fibonacci matrix

For `M = !![1, 1; 1, 0]` we have `t = 1`, `d = −1`, so the recursion becomes
`u (k+2) = u (k+1) + u k` — the Fibonacci recurrence.  The closed form then
reproduces the classical identity `Mⁿ⁺¹ = F (n+1) • M + F n • 1`, i.e.
`Mⁿ = !![F (n+1), F n; F n, F (n−1)]` (here shown via the `n = 2` instance
`M² = !![2, 1; 1, 1]`).

## Mathlib input

* `Matrix.charpoly_fin_two` : `χ_M = X² − C(tr M)·X + C(det M)`.
* `Matrix.aeval_self_charpoly` : `χ_M(M) = 0` (Cayley–Hamilton).

Everything else is built here.  All results are fully machine-checked:
`0 sorry`, `0 axiom`, no `native_decide`.
-/

namespace CayleyHamiltonClosedForm

open Matrix Polynomial

variable {R : Type*} [CommRing R]

/-- The **Lucas sequence of the first kind** attached to the monic quadratic
`X² − t·X + d` (the characteristic polynomial of a `2×2` matrix of trace `t` and
determinant `d`).  It satisfies `u 0 = 0`, `u 1 = 1`,
`u (k+2) = t · u (k+1) − d · u k`. -/
def lucasU (t d : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => t * lucasU t d (n + 1) - d * lucasU t d n

@[simp] theorem lucasU_zero (t d : R) : lucasU t d 0 = 0 := rfl

@[simp] theorem lucasU_one (t d : R) : lucasU t d 1 = 1 := rfl

/-- The defining two-step recurrence for the Lucas sequence. -/
theorem lucasU_add_two (t d : R) (n : ℕ) :
    lucasU t d (n + 2) = t * lucasU t d (n + 1) - d * lucasU t d n := rfl

/-- **Cayley–Hamilton in the `2×2` case.**  `M² = (tr M) • M − (det M) • 1`. -/
theorem sq_eq_trace_smul_sub_det_smul [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R) :
    M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  have h := M.aeval_self_charpoly
  rw [M.charpoly_fin_two] at h
  simp only [map_add, map_sub, map_pow, aeval_X, aeval_mul, aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h
  -- `h : M ^ 2 - M.trace • M + M.det • 1 = 0`
  refine eq_of_sub_eq_zero ?_
  rw [show M ^ 2 - (M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) R))
        = M ^ 2 - M.trace • M + M.det • (1 : Matrix (Fin 2) (Fin 2) R) by abel]
  exact h

/-- **Closed-form powers of a `2×2` matrix.**

`Mⁿ⁺¹ = u(n+1) • M − (det M · u n) • 1`, where `u = lucasU (tr M) (det M)` is the
Lucas sequence of the characteristic polynomial.  Every power of `M` is an explicit
affine combination of `M` and the identity, with scalar coefficients governed by a
single second-order linear recurrence. -/
theorem pow_succ_eq_lucasU_smul [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    M ^ (n + 1)
      = lucasU M.trace M.det (n + 1) • M
        - (M.det * lucasU M.trace M.det n) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ih, lucasU_add_two]
    rw [mul_sub, mul_smul_comm, mul_smul_comm, ← pow_two,
      sq_eq_trace_smul_sub_det_smul M, mul_one]
    match_scalars <;> ring

/-- Reindexed form for a strictly positive exponent: `Mⁿ = u n • M − (det M · u(n−1)) • 1`. -/
theorem pow_eq_lucasU_smul [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R) (n : ℕ) (hn : 0 < n) :
    M ^ n
      = lucasU M.trace M.det n • M
        - (M.det * lucasU M.trace M.det (n - 1)) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  simpa using pow_succ_eq_lucasU_smul M m

/-! ### Showcase: the Fibonacci matrix `!![1,1; 1,0]` -/

/-- The Fibonacci matrix. -/
def fibMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

@[simp] theorem fibMatrix_trace : fibMatrix.trace = 1 := by
  simp [fibMatrix, Matrix.trace_fin_two]

@[simp] theorem fibMatrix_det : fibMatrix.det = -1 := by
  simp [fibMatrix, Matrix.det_fin_two]

/-- For the Fibonacci matrix the Lucas recursion `u(k+2) = u(k+1) + u k` is exactly
the Fibonacci recurrence, and the closed form gives `M² = u 2 • M − det • u 1 • 1`,
i.e. `!![2,1; 1,1]`. -/
theorem fibMatrix_sq :
    fibMatrix ^ 2 = !![2, 1; 1, 1] := by
  rw [pow_succ_eq_lucasU_smul fibMatrix 1]
  simp only [fibMatrix_trace, fibMatrix_det, lucasU_add_two, lucasU_one, lucasU_zero]
  norm_num [fibMatrix]
  decide

end CayleyHamiltonClosedForm
