import Mathlib

/-
# The matrix form of Cassini's identity: `det(Qⁿ) = (−1)ⁿ`

`fibonacci-identities-oq-04-oq-01` proved Vajda's identity for the Gibonacci
(Horadam) sequences and recovered Cassini, Catalan, d'Ocagne and Gelin–Cesàro as
corollaries — all by *algebraic* manipulation of the closed form
`G n = a·F n + b·F(n−1)`.

This entry supplies the **linear-algebra proof of Cassini's identity**, the first
open question of that parent.  Let

  `Q = [[1, 1], [1, 0]]`.

The single structural fact is the **Fibonacci `Q`-matrix identity**

  `Qⁿ⁺¹ = [[F(n+2), F(n+1)], [F(n+1), F n]]`,

proved by induction using only `Qⁿ⁺² = Qⁿ⁺¹ · Q` and the recurrence
`F(n+2) = F n + F(n+1)`.  Cassini then drops out of **multiplicativity of the
determinant**:

  `det(Qⁿ⁺¹) = (det Q)ⁿ⁺¹ = (−1)ⁿ⁺¹`,

while the `2×2` determinant of the right-hand side is
`F(n+2)·F n − F(n+1)²`.  Equating the two gives

  `F(n+2)·F n − F(n+1)² = (−1)ⁿ⁺¹`,

which is Cassini's identity.  Re-indexing recovers the textbook form
`F(n−1)·F(n+1) − F n² = (−1)ⁿ`.

This is a genuinely different proof from the parent: there the sign `(−1)ⁿ` came
from a parity lemma about `(−1)^|x|`; here it is *the determinant of `Q` raised to
a power* — the conceptual reason Cassini's sign alternates.  The whole development
is over `ℤ` matrices.  No axioms, no `sorry`, no `native_decide`.
-/

namespace FibonacciIdentitiesOQ04OQ01OQ01

open Matrix

/-- The Fibonacci `Q`-matrix `Q = [[1, 1], [1, 0]]` over `ℤ`. -/
def Q : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

/-- `det Q = −1`.  This `−1` is the entire source of Cassini's alternating sign. -/
@[simp] theorem det_Q : Q.det = -1 := by
  simp [Q, det_fin_two_of]

/-- **The Fibonacci `Q`-matrix identity.**

  `Qⁿ⁺¹ = [[F(n+2), F(n+1)], [F(n+1), F n]]`.

Indexing from `n+1` keeps every entry a genuine (non-negative-index) Fibonacci
number, so the base case is just `Q¹ = Q`. -/
theorem Q_pow (n : ℕ) :
    Q ^ (n + 1)
      = !![(Nat.fib (n + 2) : ℤ), (Nat.fib (n + 1) : ℤ);
            (Nat.fib (n + 1) : ℤ), (Nat.fib n : ℤ)] := by
  induction n with
  | zero =>
    rw [pow_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q, Nat.fib_one, Nat.fib_two, Nat.fib_zero]
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Q,
        show k + 1 + 2 = k + 2 + 1 from rfl, show k + 1 + 1 = k + 2 from rfl] <;>
      push_cast [Nat.fib_add_two] <;> ring

/-- `det(Qⁿ⁺¹) = (−1)ⁿ⁺¹` by multiplicativity of the determinant. -/
theorem det_Q_pow (n : ℕ) : (Q ^ (n + 1)).det = (-1 : ℤ) ^ (n + 1) := by
  rw [det_pow, det_Q]

/-- **Cassini's identity, matrix form.**

  `F(n+2)·F n − F(n+1)² = (−1)ⁿ⁺¹`.

The left side is `det` of the `Q`-matrix identity's right-hand side; the right side
is `det(Qⁿ⁺¹) = (det Q)ⁿ⁺¹`. -/
theorem cassini_matrix (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * Nat.fib n - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  have h := det_Q_pow n
  rw [Q_pow n, det_fin_two_of] at h
  -- `det !![F(n+2), F(n+1); F(n+1), F n] = F(n+2)·F n − F(n+1)·F(n+1)`
  linear_combination h

/-- **Cassini's identity, textbook indexing.**

  `F(n−1)·F(n+1) − F n² = (−1)ⁿ`   for `n ≥ 1`.

Obtained from `cassini_matrix` at `n − 1`. -/
theorem cassini_classic (n : ℕ) (hn : 1 ≤ n) :
    (Nat.fib (n - 1) : ℤ) * Nat.fib (n + 1) - (Nat.fib n : ℤ) ^ 2 = (-1) ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  -- now the index is `0 + m + 1 = m + 1`
  simp only [Nat.zero_add, Nat.add_sub_cancel]
  have h := cassini_matrix m
  -- `F(m+2)·F m − F(m+1)² = (−1)^(m+1)`; rewrite `m+1` index target accordingly
  rw [show m + 1 + 1 = m + 2 from rfl]
  linear_combination h

/-- **Cassini over `ℤ`-indexed Fibonacci**, recovering the parent's statement.

  `F(n+1)·F(n−1) − F n² = (−1)ⁿ`  for `n : ℤ`,

stated with `Int.fib`.  For non-negative indices this is exactly `cassini_classic`
transported across `Int.fib_natCast`; it agrees with Mathlib's
`Int.fib_succ_mul_fib_pred_sub_fib_sq`, but the proof here flows from the `Q`-matrix
determinant rather than from `Int`-level algebra. -/
theorem cassini_int_nonneg (n : ℕ) (hn : 1 ≤ n) :
    Int.fib ((n : ℤ) + 1) * Int.fib ((n : ℤ) - 1) - Int.fib (n : ℤ) ^ 2 = (-1) ^ n := by
  have h := cassini_classic n hn
  have e1 : Int.fib ((n : ℤ) + 1) = (Nat.fib (n + 1) : ℤ) := by
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, Int.fib_natCast]
  have e2 : Int.fib ((n : ℤ) - 1) = (Nat.fib (n - 1) : ℤ) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    rw [show ((0 + m + 1 : ℕ) : ℤ) - 1 = ((m : ℕ) : ℤ) by push_cast; ring, Int.fib_natCast]
    simp
  have e3 : Int.fib (n : ℤ) = (Nat.fib n : ℤ) := Int.fib_natCast n
  rw [e1, e2, e3]
  linear_combination h

end FibonacciIdentitiesOQ04OQ01OQ01
