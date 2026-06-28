/-
  Fibonacci identities from the Q-matrix factorisation `Q^(m+n) = Q^m Q^n`
  (open question `cassini-identity-oq-01-oq-02`)

  Parent `cassini-identity-oq-01` establishes Cassini's identity
  `F_{n+1} F_{n-1} − F_n² = (−1)ⁿ` from `det (Qⁿ) = (det Q)ⁿ`, where
  `Q = !![1,1; 1,0]` is the Fibonacci companion ("Q-")matrix.

  Its open question asks: can the **addition formula** be read off directly from the
  entries of the matrix law `Q^{m+n} = Q^m Q^n` (which is just associativity of matrix
  multiplication / `pow_add`), packaging several classical Fibonacci identities as
  corollaries of a single factorisation, with no separate induction per identity?

  This file does exactly that. The one inductive input is the closed form of the matrix
  power (`Q_pow_succ`); every identity below is then a corollary obtained by reading off a
  matrix entry of `Q^{(m+1)+(n+1)} = Q^{m+1} Q^{n+1}`, or by taking a determinant.

  - `Q_pow_succ`     : `Q^(n+1) = !![F(n+2), F(n+1); F(n+1), F(n)]`  (the only induction).
  - `fib_add_matrix` : `F(m+n+1) = F(m+1)F(n+1) + F(m)F(n)`  — the `(2,2)` entry
                       (recovers Mathlib's `Nat.fib_add`).
  - `fib_add_offdiag`: `F(m+n+2) = F(m+2)F(n+1) + F(m+1)F(n)`  — the `(1,2)` entry, the
                       "addition formula" of the problem statement.
  - `cassini_matrix` : `F(n+2)F(n) − F(n+1)² = (−1)^(n+1)`  — from `det (Q^(n+1))`, the
                       Cassini identity recovered through the *same* factorisation.
  - `fib_two_mul_add_one` : `F(2n+1) = F(n+1)² + F(n)²`  — the `m = n` diagonal of
                       `fib_add_matrix` (odd-index duplication).
  - `fib_two_mul_add_two` : `F(2n+2) = F(n+2)F(n+1) + F(n+1)F(n)`  — the `m = n` diagonal
                       of `fib_add_offdiag` (even-index duplication).

  Worked over `ℤ` (entries `(Nat.fib k : ℤ)`), 0 sorries, 0 axioms. Mathlib has no
  Fibonacci Q-matrix of its own, so the closed form `Q_pow_succ` is a genuinely new
  artifact.
-/

import Mathlib

open Matrix

namespace CassiniIdentityOQ01OQ02

/-- The Fibonacci companion ("Q-")matrix over `ℤ`: `Q = !![1,1; 1,0]`. Its powers encode
the Fibonacci numbers (`Q_pow_succ`), and `det Q = −1` drives Cassini's identity. -/
def Q : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

/-- **Closed form of the Q-matrix power** (the single induction of this development):
`Q^(n+1) = !![F(n+2), F(n+1); F(n+1), F(n)]`. The shifted exponent `n+1` keeps every
Fibonacci index nonnegative, sidestepping the `F_{-1}` convention. -/
theorem Q_pow_succ (n : ℕ) :
    Q ^ (n + 1)
      = !![(Nat.fib (n + 2) : ℤ), (Nat.fib (n + 1) : ℤ);
            (Nat.fib (n + 1) : ℤ), (Nat.fib n : ℤ)] := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Q, pow_one]
  | succ k ih =>
      have F2 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        exact_mod_cast Nat.fib_add_two
      have F3 : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        exact_mod_cast (Nat.fib_add_two (n := k + 1))
      rw [pow_succ, ih, show Q = !![(1 : ℤ), 1; 1, 0] from rfl, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.of_apply,
          Matrix.empty_val',
          show (k + 1 + 2 : ℕ) = k + 3 from rfl, show (k + 1 + 1 : ℕ) = k + 2 from rfl] <;>
        push_cast <;>
        simp only [F2, F3, mul_one, mul_zero, add_zero] <;> ring

/-- The matrix law `Q^{(m+1)+(n+1)} = Q^{m+1} · Q^{n+1}` with both sides put in closed
form: the LHS is the closed power of `Q^{(m+n+1)+1}`, the RHS the product of the two
closed powers. Every addition identity below is one entry of this single equation. -/
private theorem Q_factor (m n : ℕ) :
    (!![(Nat.fib (m + n + 3) : ℤ), (Nat.fib (m + n + 2) : ℤ);
         (Nat.fib (m + n + 2) : ℤ), (Nat.fib (m + n + 1) : ℤ)]
      : Matrix (Fin 2) (Fin 2) ℤ)
      = !![(Nat.fib (m + 2) : ℤ), (Nat.fib (m + 1) : ℤ);
            (Nat.fib (m + 1) : ℤ), (Nat.fib m : ℤ)]
        * !![(Nat.fib (n + 2) : ℤ), (Nat.fib (n + 1) : ℤ);
              (Nat.fib (n + 1) : ℤ), (Nat.fib n : ℤ)] := by
  have hexp : (m + 1) + (n + 1) = (m + n + 1) + 1 := by ring
  have hmat : Q ^ ((m + n + 1) + 1) = Q ^ (m + 1) * Q ^ (n + 1) := by
    rw [← hexp, ← pow_add]
  rw [Q_pow_succ, Q_pow_succ, Q_pow_succ] at hmat
  -- normalise the LHS Fibonacci indices `(m+n+1)+2`, `(m+n+1)+1` to `m+n+3`, `m+n+2`
  simpa only [show (m + n + 1 + 2 : ℕ) = m + n + 3 from rfl,
    show (m + n + 1 + 1 : ℕ) = m + n + 2 from rfl] using hmat

/-- **Addition formula, `(2,2)` entry.** `F(m+n+1) = F(m+1)F(n+1) + F(m)F(n)`.
This is the bottom-right entry of `Q^{(m+1)+(n+1)} = Q^{m+1} Q^{n+1}`; it recovers
Mathlib's `Nat.fib_add` as an entry of the matrix factorisation rather than by its own
induction. -/
theorem fib_add_matrix (m n : ℕ) :
    Nat.fib (m + n + 1) = Nat.fib (m + 1) * Nat.fib (n + 1) + Nat.fib m * Nat.fib n := by
  have h := congrFun (congrFun (Q_factor m n) 1) 1
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.empty_val',
    Matrix.mul_apply, Fin.sum_univ_two] at h
  exact_mod_cast h

/-- **Addition formula, `(1,2)` entry** — the form in the problem statement.
`F(m+n+2) = F(m+2)F(n+1) + F(m+1)F(n)`, read off the top-right entry of
`Q^{(m+1)+(n+1)} = Q^{m+1} Q^{n+1}`. -/
theorem fib_add_offdiag (m n : ℕ) :
    Nat.fib (m + n + 2) = Nat.fib (m + 2) * Nat.fib (n + 1) + Nat.fib (m + 1) * Nat.fib n := by
  have h := congrFun (congrFun (Q_factor m n) 0) 1
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.empty_val',
    Matrix.mul_apply, Fin.sum_univ_two] at h
  exact_mod_cast h

/-- **Cassini's identity from the same factorisation.** `F(n+2)F(n) − F(n+1)² = (−1)^(n+1)`,
obtained from `det (Q^(n+1)) = (det Q)^(n+1)` with `det Q = −1`. This is the parent
entry's identity recovered through the Q-matrix used here for the addition formulas, so a
single matrix `Q` packages both the addition law and Cassini. -/
theorem cassini_matrix (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * Nat.fib n - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  have hdet : (Q ^ (n + 1)).det = (Q.det) ^ (n + 1) := Matrix.det_pow _ _
  rw [Q_pow_succ, Matrix.det_fin_two_of, show Q = !![(1 : ℤ), 1; 1, 0] from rfl,
    Matrix.det_fin_two_of] at hdet
  -- hdet : F(n+2)·F(n) − F(n+1)·F(n+1) = (1·0 − 1·1)^(n+1)
  rw [sq, hdet]
  norm_num

/-!
## Duplication formulas (the diagonal `m = n` of the factorisation)

Setting `m = n` in the addition formulas — i.e. reading the entries of the *square*
`Q^{n+1} · Q^{n+1} = Q^{2n+2}` — collapses them to the classical Fibonacci *duplication*
identities. No new induction is needed: these are immediate corollaries of
`fib_add_matrix` / `fib_add_offdiag` at `m = n`.
-/

/-- **Odd-index duplication.** `F(2n+1) = F(n+1)² + F(n)²` — the `m = n` case of
`fib_add_matrix`, the `(2,2)` entry of `Q^{n+1} · Q^{n+1}`. The classical fact that
`F_{2n+1}` is a sum of two consecutive Fibonacci squares. -/
theorem fib_two_mul_add_one (n : ℕ) :
    Nat.fib (2 * n + 1) = Nat.fib (n + 1) ^ 2 + Nat.fib n ^ 2 := by
  have h := fib_add_matrix n n
  rw [show 2 * n + 1 = n + n + 1 from by ring, sq, sq, h]

/-- **Even-index duplication.** `F(2n+2) = F(n+2)F(n+1) + F(n+1)F(n)` — the `m = n` case of
`fib_add_offdiag`, the `(1,2)` entry of `Q^{n+1} · Q^{n+1}`. Equivalently
`F(2n+2) = F(n+1)·(F(n+2) + F(n))`. -/
theorem fib_two_mul_add_two (n : ℕ) :
    Nat.fib (2 * n + 2)
      = Nat.fib (n + 2) * Nat.fib (n + 1) + Nat.fib (n + 1) * Nat.fib n := by
  have h := fib_add_offdiag n n
  rw [show 2 * n + 2 = n + n + 2 from by ring, h]

end CassiniIdentityOQ01OQ02
