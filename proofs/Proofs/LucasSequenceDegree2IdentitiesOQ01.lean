import Mathlib.Tactic
import Proofs.LucasSequenceDegree2Identities

/-
# General Lucas-Sequence Doubling Formulas

## Open Question answered (parent OQ-01)

The parent entry `LucasSequenceDegree2Identities` proves the master degree-2 identity
`Vₙ² − D·Uₙ² = 4·Qⁿ` for the two-parameter Lucas sequences `Uₙ(P,Q)`, `Vₙ(P,Q)` and
records, as its first open question, the *doubling* (index-halving) formulas

  **`U₂ₙ = Uₙ·Vₙ`**   and   **`V₂ₙ = Vₙ² − 2·Qⁿ`**.

These are the arithmetic heart of the theory: they express a Lucas number of index `2n`
through its value at `n`, giving the `O(log n)` *fast-doubling* algorithm and the squaring
step `Vₙ ↦ V₂ₙ = Vₙ² − 2·Qⁿ` of the Lucas–Lehmer primality test.

## Proof architecture (no Binet closed form, no `√D`)

1. `U_double_pair` — the **fast-doubling pair**
   `U₂ₙ = Uₙ·Vₙ` and `U₂ₙ₊₁ = Uₙ₊₁² − Q·Uₙ²`, proved by a single *simultaneous*
   induction on `n`.  Pairing the two consecutive doubled indices `2n`, `2n+1` closes
   the second-order recurrence `Uₘ₊₂ = P·Uₘ₊₁ − Q·Uₘ`; eliminating the companion value
   through `V_eq` (`Vₖ = 2·Uₖ₊₁ − P·Uₖ`) collapses each step to a ring identity in `U`.

2. `V_two_mul`, `V_two_mul_add_one` — the **companion doubling laws**
   `V₂ₙ = Vₙ² − 2·Qⁿ` and `V₂ₙ₊₁ = Vₙ₊₁·Vₙ − P·Qⁿ`, with **no further induction**:
   rewrite `V₂ₖ` through `V_eq`, insert the fast-doubling pair, eliminate `Vₙ` again by
   `V_eq`, and discharge the residual `Qⁿ` with the parent's invariant quadratic form
   `U_quad` (`Uₙ₊₁² − P·Uₙ·Uₙ₊₁ + Q·Uₙ² = Qⁿ`) via `linear_combination`.

The whole development is uniform in `(P,Q)`: the Fibonacci/Lucas doubling
`F₂ₙ = Fₙ·Lₙ`, `L₂ₙ = Lₙ² − 2·(−1)ⁿ` and the Pell doubling are the `(1,−1)` and
`(2,−1)` instances.

## Axioms: 0 | Sorries: 0
-/

namespace LucasSequenceDegree2Identities

/-! ## Section I: The Fast-Doubling Pair -/

/-- **Fast-doubling pair.** Simultaneously
`U₂ₙ = Uₙ·Vₙ` and `U₂ₙ₊₁ = Uₙ₊₁² − Q·Uₙ²`.

Proved by one induction on `n`: the successor step expands the recurrence at the doubled
index `2k`, feeds in the inductive pair, eliminates the companion values via `V_eq`, and
closes each equality by `ring`.  Index normalization `2·(k+1) = 2k+2`,
`2·(k+1)+1 = 2k+3` is handled definitionally by `show`. -/
theorem U_double_pair (P Q : ℤ) (n : ℕ) :
    U P Q (2 * n) = U P Q n * V P Q n ∧
    U P Q (2 * n + 1) = (U P Q (n + 1)) ^ 2 - Q * (U P Q n) ^ 2 := by
  induction n with
  | zero => exact ⟨by simp, by simp⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    -- Recurrence at the doubled indices, with clean index forms.
    have h22 : U P Q (2 * k + 2) = P * U P Q (2 * k + 1) - Q * U P Q (2 * k) :=
      U_add_two P Q (2 * k)
    have h23 : U P Q (2 * k + 3) = P * U P Q (2 * k + 2) - Q * U P Q (2 * k + 1) :=
      U_add_two P Q (2 * k + 1)
    -- Companion values in terms of `U`.
    have hVk : V P Q k = 2 * U P Q (k + 1) - P * U P Q k := V_eq P Q k
    have hUk2 : U P Q (k + 2) = P * U P Q (k + 1) - Q * U P Q k := U_add_two P Q k
    refine ⟨?_, ?_⟩
    · show U P Q (2 * k + 2) = U P Q (k + 1) * V P Q (k + 1)
      rw [h22, ih2, ih1, hVk, V_eq P Q (k + 1), hUk2]
      ring
    · show U P Q (2 * k + 3) = (U P Q (k + 2)) ^ 2 - Q * (U P Q (k + 1)) ^ 2
      rw [h23, h22, ih2, ih1, hVk, hUk2]
      ring

/-- **Fundamental doubling formula** `U₂ₙ = Uₙ·Vₙ` (the OQ-01 first target). -/
theorem U_two_mul (P Q : ℤ) (n : ℕ) : U P Q (2 * n) = U P Q n * V P Q n :=
  (U_double_pair P Q n).1

/-- **Odd fast-doubling formula** `U₂ₙ₊₁ = Uₙ₊₁² − Q·Uₙ²`. -/
theorem U_two_mul_add_one (P Q : ℤ) (n : ℕ) :
    U P Q (2 * n + 1) = (U P Q (n + 1)) ^ 2 - Q * (U P Q n) ^ 2 :=
  (U_double_pair P Q n).2

/-! ## Section II: Companion Doubling -/

/-- **Companion doubling formula** `V₂ₙ = Vₙ² − 2·Qⁿ` (the OQ-01 second target).

No induction: `V_eq` turns `V₂ₙ` into `2·U₂ₙ₊₁ − P·U₂ₙ`, the fast-doubling pair evaluates
both `U`-terms, `V_eq` eliminates the remaining `Vₙ`, and the residual `Qⁿ` is supplied by
the invariant quadratic form `U_quad` with coefficient `−2`. -/
theorem V_two_mul (P Q : ℤ) (n : ℕ) :
    V P Q (2 * n) = (V P Q n) ^ 2 - 2 * Q ^ n := by
  have hV2 : V P Q (2 * n) = 2 * U P Q (2 * n + 1) - P * U P Q (2 * n) := V_eq P Q (2 * n)
  rw [hV2, U_two_mul_add_one, U_two_mul, V_eq P Q n]
  linear_combination (-2 : ℤ) * U_quad P Q n

/-- **Odd companion doubling** `V₂ₙ₊₁ = Vₙ₊₁·Vₙ − P·Qⁿ`.

Same shape: `V_eq` at `2n+1` needs `U₂ₙ₊₂ = U₂₍ₙ₊₁₎ = Uₙ₊₁·Vₙ₊₁` (fast-doubling pair at
`n+1`) and `U₂ₙ₊₁`; eliminating the companion values and reducing `Qⁿ` by `U_quad`
(coefficient `−P`) closes it. -/
theorem V_two_mul_add_one (P Q : ℤ) (n : ℕ) :
    V P Q (2 * n + 1) = V P Q (n + 1) * V P Q n - P * Q ^ n := by
  have hV2 : V P Q (2 * n + 1) = 2 * U P Q (2 * n + 2) - P * U P Q (2 * n + 1) :=
    V_eq P Q (2 * n + 1)
  have hU2 : U P Q (2 * n + 2) = U P Q (n + 1) * V P Q (n + 1) :=
    U_two_mul P Q (n + 1)
  have hUn2 : U P Q (n + 2) = P * U P Q (n + 1) - Q * U P Q n := U_add_two P Q n
  rw [hV2, hU2, U_two_mul_add_one, V_eq P Q (n + 1), V_eq P Q n, hUn2]
  linear_combination (-P) * U_quad P Q n

/-! ## Section III: Named Specializations and Numeric Checks -/

/-- Fibonacci doubling `F₂ₙ = Fₙ·Lₙ`, the `(P,Q) = (1,−1)` instance. -/
theorem fib_doubling (n : ℕ) : U 1 (-1) (2 * n) = U 1 (-1) n * V 1 (-1) n :=
  U_two_mul 1 (-1) n

/-- Lucas doubling `L₂ₙ = Lₙ² − 2·(−1)ⁿ`, the `(P,Q) = (1,−1)` instance. -/
theorem lucas_doubling (n : ℕ) :
    V 1 (-1) (2 * n) = (V 1 (-1) n) ^ 2 - 2 * (-1 : ℤ) ^ n :=
  V_two_mul 1 (-1) n

/-- Pell doubling `U₂ₙ = Uₙ·Vₙ`, the `(P,Q) = (2,−1)` instance. -/
theorem pell_doubling (n : ℕ) : U 2 (-1) (2 * n) = U 2 (-1) n * V 2 (-1) n :=
  U_two_mul 2 (-1) n

/-- Numeric sanity check at `(1,−1)`, `n = 3`: `F₆ = 8 = F₃·L₃ = 2·4` and
`L₆ = 18 = L₃² − 2·(−1)³ = 16 + 2`. -/
example : U 1 (-1) 6 = 8 ∧ V 1 (-1) 6 = 18 ∧
    U 1 (-1) 6 = U 1 (-1) 3 * V 1 (-1) 3 ∧
    V 1 (-1) 6 = (V 1 (-1) 3) ^ 2 - 2 * (-1 : ℤ) ^ 3 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end LucasSequenceDegree2Identities
