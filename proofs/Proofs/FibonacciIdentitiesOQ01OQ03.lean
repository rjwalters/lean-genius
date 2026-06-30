/-
# Cassini's Identity via the Fibonacci Q-matrix

This file answers the third open question of `fibonacci-identities-oq-01`
(Cassini's identity): **derive Cassini matrix-theoretically** as
`det (Q ^ n) = (-1) ^ n`, where `Q = !![1, 1; 1, 0]` is the Fibonacci
Q-matrix.

The mechanism is the classical observation that powers of `Q` collect
consecutive Fibonacci numbers,

  `Q ^ (n + 1) = !![F (n+2), F (n+1); F (n+1), F n]`,

proved by a single induction using only the Fibonacci recurrence
`Nat.fib_add_two` and the explicit two-by-two product `Matrix.mul_fin_two`.
Taking determinants two ways then forces Cassini's identity:

  * multiplicativity of `det` gives `det (Q ^ (n+1)) = (det Q) ^ (n+1) = (-1) ^ (n+1)`;
  * the explicit entries give `det (Q ^ (n+1)) = F (n+2) · F n − F (n+1) ^ 2`.

Equating the two yields `F (n+2) · F n − F (n+1) ^ 2 = (-1) ^ (n+1)`
(`fib_cassini_matrix`), and re-indexing recovers the parent's named form
`F (n+1) · F (n-1) − F n ^ 2 = (-1) ^ n` for `n ≥ 1` (`fib_cassini`).

Mathlib carries Cassini's identity over `ℤ` directly
(`Int.fib_add_one_mul_fib_sub_one_sub_fib_sq` style), but **not** the
Q-matrix derivation: there is no `Q ^ n = fib`-matrix lemma in Mathlib, so
the matrix engine here (`Q_pow_succ`) is an original contribution.

Worked numerics: `det (Q^3) = F 4 · F 2 − F 3 ^ 2 = 3·1 − 2² = -1 = (-1)^3`;
`det (Q^4) = F 5 · F 3 − F 4 ^ 2 = 5·2 − 3² = 1 = (-1)^4`.
-/
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace FibonacciIdentitiesOQ01OQ03

open Nat Matrix

/-- The Fibonacci **Q-matrix** `Q = !![1, 1; 1, 0]` over `ℤ`. -/
def Q : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

/-- Congruence helper: two explicit `2×2` matrices agree when their entries do. -/
private theorem mateq {a b c d e f g h : ℤ}
    (h₁ : a = e) (h₂ : b = f) (h₃ : c = g) (h₄ : d = h) :
    !![a, b; c, d] = !![e, f; g, h] := by
  rw [h₁, h₂, h₃, h₄]

/-- `det Q = -1`: the Q-matrix has determinant `-1`. -/
theorem det_Q : Q.det = -1 := by
  simp [Q, Matrix.det_fin_two_of]

/-- **Q-matrix engine.** Powers of the Fibonacci Q-matrix carry consecutive
Fibonacci numbers:
`Q ^ (n + 1) = !![F (n+2), F (n+1); F (n+1), F n]`.

This is the matrix fact absent from Mathlib; everything else follows from it
by taking determinants. Proved by induction on `n` using only the Fibonacci
recurrence and the explicit two-by-two product. -/
theorem Q_pow_succ (n : ℕ) :
    Q ^ (n + 1)
      = !![(fib (n + 2) : ℤ), (fib (n + 1) : ℤ);
           (fib (n + 1) : ℤ), (fib n : ℤ)] := by
  induction n with
  | zero =>
      rw [Nat.zero_add, pow_one, Q]
      apply mateq <;> simp [Nat.fib_zero, Nat.fib_one, Nat.fib_two]
  | succ n ih =>
      have e2 : (fib (n + 2) : ℤ) = fib n + fib (n + 1) := by
        have : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
        exact_mod_cast this
      have e3 : (fib (n + 3) : ℤ) = fib (n + 1) + fib (n + 2) := by
        have : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
        exact_mod_cast this
      rw [pow_succ, ih, Q, Matrix.mul_fin_two]
      apply mateq
      · rw [show n + 1 + 2 = n + 3 from rfl, e3]; ring
      · rw [show n + 1 + 1 = n + 2 from rfl]; ring
      · rw [show n + 1 + 1 = n + 2 from rfl, e2]; ring
      · ring

/-- Determinant of `Q ^ (n+1)` via multiplicativity: `det (Q^(n+1)) = (-1)^(n+1)`. -/
theorem det_Q_pow (n : ℕ) : (Q ^ (n + 1)).det = (-1 : ℤ) ^ (n + 1) := by
  rw [Matrix.det_pow, det_Q]

/-- **Cassini's identity, matrix-theoretic form.**
Computing `det (Q ^ (n+1))` two ways forces
`F (n+2) · F n − F (n+1) ^ 2 = (-1) ^ (n+1)`. -/
theorem fib_cassini_matrix (n : ℕ) :
    (fib (n + 2) : ℤ) * fib n - (fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  have h := det_Q_pow n
  rw [Q_pow_succ, Matrix.det_fin_two_of] at h
  rw [← h]; ring

/-- **Cassini's identity, named form** (the parent statement), recovered from the
matrix derivation: for `n ≥ 1`,
`F (n+1) · F (n-1) − F n ^ 2 = (-1) ^ n`. -/
theorem fib_cassini (n : ℕ) (hn : 1 ≤ n) :
    (fib (n + 1) : ℤ) * fib (n - 1) - (fib n : ℤ) ^ 2 = (-1) ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  simpa [Nat.add_sub_cancel] using fib_cassini_matrix m

/-! ### Numeric sanity checks -/

example : (Q ^ 3).det = (-1 : ℤ) ^ 3 := by decide
example : (fib 4 : ℤ) * fib 2 - (fib 3 : ℤ) ^ 2 = (-1) ^ 3 := by decide
example : (fib 5 : ℤ) * fib 3 - (fib 4 : ℤ) ^ 2 = (-1) ^ 4 := by decide

end FibonacciIdentitiesOQ01OQ03
