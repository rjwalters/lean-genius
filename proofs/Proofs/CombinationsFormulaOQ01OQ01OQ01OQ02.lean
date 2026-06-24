/-
# Lucas analogue of Cassini's identity via the Q-matrix

This file answers the **second open question** of
`combinations-formula-oq-01-oq-01-oq-01`
("Companion Lucas-number shallow-diagonal identities"):

  *Establish the Lucas analogue of Cassini's identity,
   `L (n-1) · L (n+1) − L n ^ 2 = (-1) ^ (n-1) · 5`, over `ℤ`.*

Mathlib has Fibonacci numbers (`Nat.fib`) and even Cassini's identity for
Fibonacci, but **no Lucas numbers at all** (only the unrelated Lucas–Lehmer
primality test).  We therefore introduce the integer Lucas sequence
`L 0 = 2, L 1 = 1, L (n+2) = L n + L (n+1)` and prove its Cassini identity
**matrix-theoretically**, mirroring the gallery's Fibonacci Q-matrix entry
`fibonacci-identities-oq-01-oq-03`.

The mechanism: the **same** Fibonacci Q-matrix `Q = !![1, 1; 1, 0]` advances
the Lucas state, so multiplying the seed `M₀ = !![3, 1; 1, 2] = !![L 2, L 1; L 1, L 0]`
on the left by `Q ^ n` collects consecutive Lucas numbers:

  `Q ^ n * M₀ = !![L (n+2), L (n+1); L (n+1), L n]`   (`Q_pow_mul_seed`).

Taking determinants two ways forces Cassini:

  * multiplicativity gives `det (Q^n * M₀) = (det Q)^n · det M₀ = (-1)^n · 5`;
  * the explicit entries give `det (Q^n * M₀) = L (n+2) · L n − L (n+1) ^ 2`.

Equating yields `L (n+2) · L n − L (n+1) ^ 2 = (-1) ^ n · 5`
(`lucas_cassini_matrix`); re-indexing recovers the parent's named form
`L (n-1) · L (n+1) − L n ^ 2 = (-1) ^ (n-1) · 5` for `n ≥ 1` (`lucas_cassini`).

The contrast with Fibonacci is the constant: the Fibonacci seed `Q` has
determinant `-1`, while the Lucas seed `M₀` has determinant `5`, so the
"discriminant" `5` of the Lucas sequence is exactly `det M₀`.

Worked numerics: `det (Q^2 * M₀) = L 4 · L 2 − L 3 ^ 2 = 7·3 − 4² = 5 = (-1)^2·5`;
`L 3 · L 1 − L 2 ^ 2 = 4·1 − 3² = -5 = (-1)^3·5`.

Everything is axiom-free.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace CombinationsFormulaOQ01OQ01OQ01OQ02

open Matrix

/-! ### The integer Lucas sequence -/

/-- The **Lucas numbers** over `ℤ`: `L 0 = 2`, `L 1 = 1`, `L (n+2) = L n + L (n+1)`,
i.e. `2, 1, 3, 4, 7, 11, 18, …`.  Mathlib has `Nat.fib` but no Lucas sequence; we
work over `ℤ` so the alternating sign in Cassini's identity is expressible. -/
def L : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | (n + 2) => L n + L (n + 1)

@[simp] theorem L_zero : L 0 = 2 := rfl
@[simp] theorem L_one : L 1 = 1 := rfl

/-- The Lucas recurrence `L (n+2) = L n + L (n+1)`. -/
theorem L_add_two (n : ℕ) : L (n + 2) = L n + L (n + 1) := rfl

/-! ### The Q-matrix engine -/

/-- The Fibonacci **Q-matrix** `Q = !![1, 1; 1, 0]` over `ℤ`.  The same matrix that
advances the Fibonacci state also advances the Lucas state. -/
def Q : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

/-- The Lucas **seed matrix** `M₀ = !![3, 1; 1, 2] = !![L 2, L 1; L 1, L 0]`. -/
def M0 : Matrix (Fin 2) (Fin 2) ℤ := !![3, 1; 1, 2]

/-- Congruence helper: two explicit `2×2` matrices agree when their entries do. -/
private theorem mateq {a b c d e f g h : ℤ}
    (h₁ : a = e) (h₂ : b = f) (h₃ : c = g) (h₄ : d = h) :
    !![a, b; c, d] = !![e, f; g, h] := by
  rw [h₁, h₂, h₃, h₄]

/-- `det Q = -1`. -/
theorem det_Q : Q.det = -1 := by
  simp [Q, Matrix.det_fin_two_of]

/-- `det M₀ = 5`: the determinant of the Lucas seed is the sequence's discriminant. -/
theorem det_M0 : M0.det = 5 := by
  simp [M0, Matrix.det_fin_two_of]

/-- **Lucas Q-matrix engine.** Left-multiplying the seed by powers of the Fibonacci
Q-matrix collects consecutive Lucas numbers:
`Q ^ n * M₀ = !![L (n+2), L (n+1); L (n+1), L n]`.

This is the matrix fact absent from Mathlib (Mathlib has neither Lucas numbers nor a
`Q ^ n`-Lucas lemma); everything else follows by taking determinants.  Proved by
induction on `n` using only the Lucas recurrence and the explicit `2×2` product. -/
theorem Q_pow_mul_seed (n : ℕ) :
    Q ^ n * M0 = !![L (n + 2), L (n + 1); L (n + 1), L n] := by
  induction n with
  | zero =>
      rw [pow_zero, one_mul, M0]
      apply mateq <;> decide
  | succ n ih =>
      have e2 : L (n + 2) = L n + L (n + 1) := L_add_two n
      have e3 : L (n + 3) = L (n + 1) + L (n + 2) := rfl
      rw [pow_succ', Matrix.mul_assoc, ih, Q, Matrix.mul_fin_two]
      apply mateq
      · rw [show n + 1 + 2 = n + 3 from rfl, e3]; ring
      · rw [show n + 1 + 1 = n + 2 from rfl, e2]; ring
      · rw [show n + 1 + 1 = n + 2 from rfl]; ring
      · ring

/-! ### Cassini's identity for Lucas numbers -/

/-- **Lucas Cassini, matrix-theoretic form.** Computing `det (Q ^ n * M₀)` two ways
forces `L (n+2) · L n − L (n+1) ^ 2 = (-1) ^ n · 5`. -/
theorem lucas_cassini_matrix (n : ℕ) :
    L (n + 2) * L n - L (n + 1) ^ 2 = (-1) ^ n * 5 := by
  have h : (Q ^ n * M0).det = (-1 : ℤ) ^ n * 5 := by
    rw [Matrix.det_mul, Matrix.det_pow, det_Q, det_M0]
  rw [Q_pow_mul_seed, Matrix.det_fin_two_of] at h
  rw [← h]; ring

/-- **Lucas Cassini, named form** (the parent's open question), recovered from the
matrix derivation: for `n ≥ 1`,
`L (n-1) · L (n+1) − L n ^ 2 = (-1) ^ (n-1) · 5`. -/
theorem lucas_cassini (n : ℕ) (hn : 1 ≤ n) :
    L (n - 1) * L (n + 1) - L n ^ 2 = (-1) ^ (n - 1) * 5 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  have h := lucas_cassini_matrix m
  show L m * L (m + 2) - L (m + 1) ^ 2 = (-1) ^ m * 5
  linear_combination h

/-! ### Numeric sanity checks -/

example : (Q ^ 2 * M0).det = (-1 : ℤ) ^ 2 * 5 := by decide
example : L 4 * L 2 - L 3 ^ 2 = (-1 : ℤ) ^ 2 * 5 := by decide
example : L 3 * L 1 - L 2 ^ 2 = (-1 : ℤ) ^ 3 * 5 := by decide

end CombinationsFormulaOQ01OQ01OQ01OQ02
