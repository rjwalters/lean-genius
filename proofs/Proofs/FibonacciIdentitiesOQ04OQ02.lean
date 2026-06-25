import Mathlib

/-
# The Fibonacci Q-matrix: `det(Qⁿ) = (−1)ⁿ` and the Cassini / Vajda identities

The classical **Q-matrix** of the Fibonacci numbers is

  `Q = !![1, 1; 1, 0]`,

whose powers encode the Fibonacci sequence:

  `Qⁿ = !![F (n+1), F n; F n, F (n+1) − F n]`   (with `F (n+1) − F n = F (n−1)`).

This file formalises the matrix form requested as an open question of the entry
*Vajda's and d'Ocagne's Identities* (`fibonacci-identities-oq-04`):

> Formalize the matrix form `det([[1,1],[1,0]]ⁿ) = (−1)ⁿ` and deduce Vajda from the
> multiplicativity of determinants.

The development is purely matrix-theoretic and self-contained over `Nat.fib`:

* `Q_pow`         — the closed form of `Qⁿ` (induction on `n`);
* `det_Q_pow`     — `det (Qⁿ) = (−1)ⁿ`, an instant corollary of `det (A·B) = det A · det B`
                    via `Matrix.det_pow`;
* `fib_cassini`   — **Cassini's identity** `F (n+1)² − F n · F (n+2) = (−1)ⁿ`, read directly
                    off `det_Q_pow` and the explicit `2×2` determinant;
* `fib_add'`      — the Fibonacci **addition law** `F (a+b) = F (a+1)·F b + F a·(F (b+1) − F b)`,
                    read off the `(0,1)` entry of `Qᵃ⁺ᵇ = Qᵃ · Qᵇ` (multiplicativity of `Q`);
* `fib_vajda`     — **Vajda's identity** `F (x+i)·F (x+j) − F x·F (x+i+j) = (−1)ˣ·F i·F j`,
                    deduced from `fib_cassini` (determinant) and `fib_add'` (multiplicativity);
* `fib_catalan`   — Catalan's identity as the `i = j` specialisation of Vajda.

Everything is over `Nat.fib` cast to `ℤ` (so the signs `(−1)ⁿ` make sense). No axioms,
no `sorry`, no `native_decide`. The Fibonacci Q-matrix and `det(Qⁿ) = (−1)ⁿ` are **absent
from Mathlib** (Mathlib records `Nat.fib_add` but no matrix encoding).
-/

namespace FibonacciIdentitiesOQ04OQ02

open Matrix

/-- The Fibonacci **Q-matrix** `!![1, 1; 1, 0]` over `ℤ`. -/
def Q : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

/-- `det Q = −1`. -/
theorem det_Q : Q.det = -1 := by
  simp [Q, Matrix.det_fin_two_of]

/-- The integer recurrence `F (n+2) = F n + F (n+1)` over `ℤ`. -/
theorem fib_rec (n : ℕ) : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
  exact_mod_cast Nat.fib_add_two

/-- **Closed form of the Q-matrix powers.**
`Qⁿ = !![F (n+1), F n; F n, F (n+1) − F n]`, where the bottom-right entry equals `F (n−1)`.
Proved by induction on `n` using only `Q · Qⁿ` and the Fibonacci recurrence. -/
theorem Q_pow (n : ℕ) :
    Q ^ n =
      !![(Nat.fib (n + 1) : ℤ), (Nat.fib n : ℤ);
         (Nat.fib n : ℤ), (Nat.fib (n + 1) : ℤ) - (Nat.fib n : ℤ)] := by
  induction n with
  | zero =>
    rw [pow_zero, Matrix.one_fin_two]
    norm_num [Nat.fib_one, Nat.fib_zero]
  | succ k ih =>
    rw [pow_succ, ih, Q]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, fib_rec k]
    all_goals ring

/-- **`det (Qⁿ) = (−1)ⁿ`** — the headline matrix identity, immediate from
`det (A·B) = det A · det B` (`Matrix.det_pow`) and `det Q = −1`. -/
theorem det_Q_pow (n : ℕ) : (Q ^ n).det = (-1) ^ n := by
  rw [Matrix.det_pow, det_Q]

/-- **Cassini's identity** `F (n+1)² − F n · F (n+2) = (−1)ⁿ`, read directly off
`det (Qⁿ) = (−1)ⁿ` by computing the determinant of the explicit `2×2` closed form. -/
theorem fib_cassini (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) = (-1) ^ n := by
  have h := det_Q_pow n
  rw [Q_pow, Matrix.det_fin_two_of] at h
  -- h : F (n+1) * (F (n+1) - F n) - F n * F n = (-1)^n
  rw [fib_rec n]
  linear_combination h

/-- **Fibonacci addition law from the Q-matrix.**
`F (a+b) = F (a+1)·F b + F a·(F (b+1) − F b)`, obtained by reading the `(0,1)` entry of
`Qᵃ⁺ᵇ = Qᵃ · Qᵇ` (multiplicativity of matrix powers). -/
theorem fib_add' (a b : ℕ) :
    (Nat.fib (a + b) : ℤ)
      = (Nat.fib (a + 1) : ℤ) * (Nat.fib b : ℤ)
        + (Nat.fib a : ℤ) * ((Nat.fib (b + 1) : ℤ) - (Nat.fib b : ℤ)) := by
  have h : Q ^ (a + b) = Q ^ a * Q ^ b := pow_add Q a b
  rw [Q_pow, Q_pow, Q_pow] at h
  have h01 := congr_fun (congr_fun h 0) 1
  simpa [Matrix.mul_apply, Fin.sum_univ_two] using h01

/-- **Vajda's identity** `F (x+i)·F (x+j) − F x·F (x+i+j) = (−1)ˣ·(F i·F j)`,
the two-parameter master identity of the Fibonacci product family.

Deduced entirely from the matrix theory above: the sign `(−1)ˣ` comes from Cassini
(`det (Qˣ) = (−1)ˣ`) and every shifted Fibonacci number is expanded with the
multiplicativity addition law `fib_add'`. -/
theorem fib_vajda (x i j : ℕ) :
    (Nat.fib (x + i) : ℤ) * (Nat.fib (x + j) : ℤ)
        - (Nat.fib x : ℤ) * (Nat.fib (x + i + j) : ℤ)
      = (-1) ^ x * ((Nat.fib i : ℤ) * (Nat.fib j : ℤ)) := by
  -- Cassini in determinant form: F(x+1)² − F(x+1)·F x − F x² = (−1)ˣ
  have hcx : (Nat.fib (x + 1) : ℤ) ^ 2
      - (Nat.fib (x + 1) : ℤ) * (Nat.fib x : ℤ) - (Nat.fib x : ℤ) ^ 2 = (-1) ^ x := by
    have h := fib_cassini x
    rw [fib_rec x] at h
    linear_combination h
  -- addition-law expansions of the three shifted indices
  have h1 := fib_add' x i
  have h2 := fib_add' x j
  have h3 := fib_add' x (i + j)
  have h4 := fib_add' i j
  -- F (i + j + 1) via `fib_add' i (j+1)` together with `F (j+2) − F (j+1) = F j`
  have h5 : (Nat.fib (i + j + 1) : ℤ)
      = (Nat.fib (i + 1) : ℤ) * (Nat.fib (j + 1) : ℤ) + (Nat.fib i : ℤ) * (Nat.fib j : ℤ) := by
    have h := fib_add' i (j + 1)
    rw [show i + (j + 1) = i + j + 1 by ring, fib_rec j] at h
    linear_combination h
  rw [show x + i + j = x + (i + j) by ring]
  rw [h1, h2, h3, h4, h5]
  linear_combination ((Nat.fib i : ℤ) * (Nat.fib j : ℤ)) * hcx

/-- **Catalan's identity** `F (x+a)² − F x · F (x+2a) = (−1)ˣ · F a²`,
the `i = j = a` specialisation of Vajda. -/
theorem fib_catalan (x a : ℕ) :
    (Nat.fib (x + a) : ℤ) ^ 2 - (Nat.fib x : ℤ) * (Nat.fib (x + 2 * a) : ℤ)
      = (-1) ^ x * (Nat.fib a : ℤ) ^ 2 := by
  have h := fib_vajda x a a
  rw [show x + a + a = x + 2 * a by ring] at h
  linear_combination h

end FibonacciIdentitiesOQ04OQ02
