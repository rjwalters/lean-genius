import Mathlib.Tactic
import Proofs.LucasSequenceDegree2Identities
import Proofs.LucasSequenceDegree2IdentitiesOQ01
import Proofs.LucasSequenceDegree2IdentitiesOQ02

/-
# General Lucas-Sequence Index-Tripling Formulas

## Open Question answered (parent OQ-01 → OQ-01)

The parent entry `LucasSequenceDegree2IdentitiesOQ01` establishes the **doubling**
(index-halving) formulas `U₂ₙ = Uₙ·Vₙ`, `V₂ₙ = Vₙ² − 2·Qⁿ` for the two-parameter
Lucas sequences `Uₙ(P,Q)`, `Vₙ(P,Q)`.  Its own open question asks for the next rung of
the index-multiplication ladder: the **tripling** formulas expressing `U₃ₙ` and `V₃ₙ`
as polynomials in `Uₙ`, `Vₙ`, `Qⁿ` alone.  This file proves them:

  **`U₃ₙ = Uₙ·(Vₙ² − Qⁿ)`**   and   **`V₃ₙ = Vₙ·(Vₙ² − 3·Qⁿ)`**.

Together with doubling these give the full `U₂ₙ, U₂ₙ₊₁, U₃ₙ, …` addition toolkit and, in
particular, the ternary (`3ⁿ`-radix) fast-exponentiation step for Lucas sequences.

## Proof architecture (no Binet closed form, no `√D`)

Both are one-line consequences of the parent's *bilinear addition laws* at the split
`3n = 2n + n`, after eliminating the doubled-index values through the doubling formulas.

1. `U_three_mul`.  Bilinear law (A) at `(2n, n)` reads
   `2·U₃ₙ = U₂ₙ·Vₙ + V₂ₙ·Uₙ`.  Substituting `U₂ₙ = Uₙ·Vₙ` and `V₂ₙ = Vₙ² − 2·Qⁿ`
   collapses the right side to `2·Uₙ·(Vₙ² − Qⁿ)` by `ring`; cancel the factor `2`.

2. `V_three_mul`.  Bilinear law (B) at `(2n, n)` reads
   `2·V₃ₙ = V₂ₙ·Vₙ + D·U₂ₙ·Uₙ` with `D = P² − 4Q`.  Insert the two doubling formulas,
   then eliminate the sole remaining `D·Uₙ²` through the master invariant
   `Vₙ² − D·Uₙ² = 4·Qⁿ` (`V_sq_sub_D_U_sq`) via `linear_combination`; the residue is
   `2·Vₙ·(Vₙ² − 3·Qⁿ)`.  Cancel the factor `2`.

No new induction is required: the entire tripling layer descends from the degree-2 master
identity already proved in the parent entry.  The development is uniform in `(P,Q)`, so the
Fibonacci/Lucas tripling `F₃ₙ = Fₙ·(Lₙ² − (−1)ⁿ)`, `L₃ₙ = Lₙ·(Lₙ² − 3·(−1)ⁿ)` and the
Pell tripling are the `(1,−1)` and `(2,−1)` instances.

## Axioms: 0 | Sorries: 0
-/

namespace LucasSequenceDegree2Identities

open LucasSequenceDegree2IdentitiesOQ02

/-! ## Section I: The General Tripling Formulas -/

/-- **Index-tripling formula for `U`.** `U₃ₙ = Uₙ·(Vₙ² − Qⁿ)`.

Bilinear law (A) at the split `3n = 2n + n` gives `2·U₃ₙ = U₂ₙ·Vₙ + V₂ₙ·Uₙ`; substitute
the doubling formulas `U₂ₙ = Uₙ·Vₙ`, `V₂ₙ = Vₙ² − 2·Qⁿ` and cancel the factor `2`. -/
theorem U_three_mul (P Q : ℤ) (n : ℕ) :
    U P Q (3 * n) = U P Q n * ((V P Q n) ^ 2 - Q ^ n) := by
  have hadd := two_U_add P Q (2 * n) n
  have hUd := U_doubling P Q n
  have hVd := V_doubling P Q n
  have hidx : 2 * n + n = 3 * n := by ring
  rw [hidx] at hadd
  have key : 2 * U P Q (3 * n) = 2 * (U P Q n * ((V P Q n) ^ 2 - Q ^ n)) := by
    rw [hadd, hUd, hVd]; ring
  exact mul_left_cancel₀ (by norm_num) key

/-- **Index-tripling formula for `V`.** `V₃ₙ = Vₙ·(Vₙ² − 3·Qⁿ)`.

Bilinear law (B) at the split `3n = 2n + n` gives `2·V₃ₙ = V₂ₙ·Vₙ + D·U₂ₙ·Uₙ`; substitute
the doubling formulas, eliminate `D·Uₙ²` through the master identity
`Vₙ² − D·Uₙ² = 4·Qⁿ`, and cancel the factor `2`. -/
theorem V_three_mul (P Q : ℤ) (n : ℕ) :
    V P Q (3 * n) = V P Q n * ((V P Q n) ^ 2 - 3 * Q ^ n) := by
  have hadd := two_V_add P Q (2 * n) n
  have hUd := U_doubling P Q n
  have hVd := V_doubling P Q n
  have hmaster := V_sq_sub_D_U_sq P Q n
  have hidx : 2 * n + n = 3 * n := by ring
  rw [hidx] at hadd
  have key : 2 * V P Q (3 * n) = 2 * (V P Q n * ((V P Q n) ^ 2 - 3 * Q ^ n)) := by
    rw [hadd, hUd, hVd]
    linear_combination (-(V P Q n)) * hmaster
  exact mul_left_cancel₀ (by norm_num) key

/-! ## Section II: Named Specializations and Numeric Checks -/

/-- Fibonacci tripling `F₃ₙ = Fₙ·(Lₙ² − (−1)ⁿ)`, the `(P,Q) = (1,−1)` instance. -/
theorem fib_tripling (n : ℕ) :
    U 1 (-1) (3 * n) = U 1 (-1) n * ((V 1 (-1) n) ^ 2 - (-1 : ℤ) ^ n) :=
  U_three_mul 1 (-1) n

/-- Lucas tripling `L₃ₙ = Lₙ·(Lₙ² − 3·(−1)ⁿ)`, the `(P,Q) = (1,−1)` instance. -/
theorem lucas_tripling (n : ℕ) :
    V 1 (-1) (3 * n) = V 1 (-1) n * ((V 1 (-1) n) ^ 2 - 3 * (-1 : ℤ) ^ n) :=
  V_three_mul 1 (-1) n

/-- Pell tripling `U₃ₙ = Uₙ·(Vₙ² − (−1)ⁿ)`, the `(P,Q) = (2,−1)` instance. -/
theorem pell_tripling (n : ℕ) :
    U 2 (-1) (3 * n) = U 2 (-1) n * ((V 2 (-1) n) ^ 2 - (-1 : ℤ) ^ n) :=
  U_three_mul 2 (-1) n

/-- Numeric sanity check at `(1,−1)`, `n = 2`: `F₆ = 8`, `F₂·(L₂² − (−1)²) = 1·(9 − 1) = 8`
and `L₆ = 18`, `L₂·(L₂² − 3·(−1)²) = 3·(9 − 3) = 18`. -/
example : U 1 (-1) 6 = 8 ∧ V 1 (-1) 6 = 18 ∧
    U 1 (-1) 6 = U 1 (-1) 2 * ((V 1 (-1) 2) ^ 2 - (-1 : ℤ) ^ 2) ∧
    V 1 (-1) 6 = V 1 (-1) 2 * ((V 1 (-1) 2) ^ 2 - 3 * (-1 : ℤ) ^ 2) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end LucasSequenceDegree2Identities
