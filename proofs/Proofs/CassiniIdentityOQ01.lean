/-
# Cassini's Identity via the Fibonacci Q-matrix

Cassini's identity states that for the Fibonacci numbers `F`,
`F_{n+2} · F_n − F_{n+1}² = (−1)^{n+1}`.

Mathlib already proves the integer-indexed form
(`Int.fib_succ_mul_fib_pred_sub_fib_sq`) by direct induction. This file gives a
conceptually *different* proof: the **linear-algebra / determinant** proof.

Let `Q = !![1, 1; 1, 0]` be the Fibonacci companion matrix. Its powers encode the
Fibonacci numbers,
`Q^{n+1} = !![F_{n+2}, F_{n+1}; F_{n+1}, F_n]`,
and `det Q = −1`. Since the determinant is multiplicative,
`det (Q^{n+1}) = (det Q)^{n+1} = (−1)^{n+1}`,
while expanding the explicit matrix gives
`det (Q^{n+1}) = F_{n+2}·F_n − F_{n+1}²`.
Equating the two evaluations yields Cassini's identity.

This realises the identity as the multiplicativity of `det` along powers of `Q`,
a connection Mathlib does not record (it has no Fibonacci matrix), and is the
standard "matrix proof" of Cassini's identity.
-/
import Mathlib

namespace CassiniIdentityOQ01

open Matrix

/-- The Fibonacci companion ("Q") matrix over `ℤ`. -/
def Q : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

/-- The determinant of the Fibonacci Q-matrix is `−1`. -/
theorem det_Q : Q.det = -1 := by
  simp [Q, Matrix.det_fin_two]

/-- **The Fibonacci matrix-power identity.**
`Q^{n+1} = !![F_{n+2}, F_{n+1}; F_{n+1}, F_n]`. The Fibonacci numbers appear as the
entries of the powers of the companion matrix. -/
theorem Q_pow_succ (n : ℕ) :
    Q ^ (n + 1) =
      !![(Nat.fib (n + 2) : ℤ), (Nat.fib (n + 1) : ℤ);
         (Nat.fib (n + 1) : ℤ), (Nat.fib n : ℤ)] := by
  induction n with
  | zero =>
    -- `Q^1 = Q = !![F_2, F_1; F_1, F_0] = !![1, 1; 1, 0]`.
    simp only [pow_one, Q, Nat.fib_zero]
    norm_num
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one] <;>
      push_cast [Nat.fib_add_two] <;> ring

/-- **Cassini's identity** (via the determinant of the Fibonacci Q-matrix):
for every `n`, `F_{n+2} · F_n − F_{n+1}² = (−1)^{n+1}`. -/
theorem cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * (Nat.fib n : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  have hdet_pow : (Q ^ (n + 1)).det = (-1) ^ (n + 1) := by
    rw [Matrix.det_pow, det_Q]
  have hdet_expand :
      (Q ^ (n + 1)).det
        = (Nat.fib (n + 2) : ℤ) * (Nat.fib n : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 := by
    rw [Q_pow_succ, Matrix.det_fin_two]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [← hdet_expand, hdet_pow]

end CassiniIdentityOQ01
