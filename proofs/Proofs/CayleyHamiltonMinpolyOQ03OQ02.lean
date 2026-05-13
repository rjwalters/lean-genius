/-
  Squared-Krylov Sequence — Structural Layer of the Keller-Gehrig Algorithm
  (cayley-hamilton-minpoly-oq-03-oq-02)

  Question: Can the O(n^ω) Keller-Gehrig algorithm (1985) be formalised,
  extending the Krylov framework (CayleyHamiltonMinpolyOQ03.lean, naive
  O(n³)) to subcubic complexity?

  This file commits to **Layer 1** of the three-layer decomposition (see
  research/problems/cayley-hamilton-minpoly-oq-03-oq-02/problem.md): the
  *structural* layer. We define the squared-Krylov sequence

      T_k := M^(2^k)

  computed by repeated squaring (T_{k+1} = T_k · T_k), and we prove the
  bridge to ordinary matrix exponentiation. This bridge is the algebraic
  fact that powers the asymptotic Keller-Gehrig speed-up: ⌈log₂ n⌉ matrix
  multiplications cover every Krylov power M^j for j < 2^⌈log₂ n⌉.

  The other two layers are explicitly *out of scope* in this iteration:

  * **Layer 2 (correctness).** Show the span of {v, Mv, ..., M^(2^k - 1) v}
    contains every Krylov vector M^j v with j < 2^k.  Tractable today; a
    follow-up scaffold.
  * **Layer 3 (complexity).** Prove the operation count is O(n^ω).
    *Blocked* on Mathlib having no complexity-monad and no fast
    (Strassen-style) matrix multiplication; any quantitative statement is
    therefore axiomatic in the current Mathlib.

  References:
  - Keller-Gehrig (1985), "Fast algorithms for the characteristic polynomial",
    Theor. Comput. Sci. 36, 309-317.
  - Giesbrecht & Storjohann (2002), "Computing rational forms of integer
    matrices", J. Symb. Comput. 34, 157-172.
  - Mathlib: `LinearAlgebra.Matrix.Charpoly.Minpoly` (used by the parent
    file `CayleyHamiltonMinpolyOQ03.lean`).

  See also:
  - `CayleyHamiltonMinpolyOQ03.lean` — naive O(n³) Krylov for μ_M.
  - `CayleyHamiltonMinpolyOQ03OQ01.lean` — vector-specific Krylov (sibling).
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Tactic

namespace MinpolyComplexity.SubcubicKrylov

variable {K : Type*} [Field K] {n : ℕ}

/-- The k-th term of the **squared-Krylov sequence**, defined by repeated
    squaring: T_0 = M, T_{k+1} = T_k · T_k. The central object of the
    Keller-Gehrig (1985) O(n^ω) algorithm — ⌈log₂ n⌉ matrix multiplications
    replace n one-step Krylov matrix-vector products. -/
def squareKrylov (M : Matrix (Fin n) (Fin n) K) : ℕ → Matrix (Fin n) (Fin n) K
  | 0     => M
  | k + 1 => squareKrylov M k * squareKrylov M k

@[simp]
theorem squareKrylov_zero (M : Matrix (Fin n) (Fin n) K) :
    squareKrylov M 0 = M := rfl

theorem squareKrylov_succ (M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    squareKrylov M (k + 1) = squareKrylov M k * squareKrylov M k := rfl

/-- **Bridge to ordinary powers.** The k-th squared-Krylov term equals
    M^(2^k). This is the algebraic content of the repeated-squaring
    identity (M^a)·(M^a) = M^(2a) iterated k times. -/
theorem squareKrylov_eq_pow_two (M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    squareKrylov M k = M ^ (2 ^ k) := by
  induction k with
  | zero =>
      show M = M ^ (2 ^ 0)
      rw [Nat.pow_zero, pow_one]
  | succ k ih =>
      show squareKrylov M k * squareKrylov M k = M ^ (2 ^ (k + 1))
      rw [ih, ← pow_add]
      congr 1
      ring

end MinpolyComplexity.SubcubicKrylov

/-
  ## Summary

  **Problem (Layer 1 of cayley-hamilton-minpoly-oq-03-oq-02).** Define the
  squared-Krylov sequence T_k := M^(2^k) via repeated squaring, and prove
  the bridge to ordinary matrix exponentiation.

  **Status.** Complete formalization of Layer 1. 3 theorems, 0 sorries.

  **Proved (3 theorems, 0 sorries).**
  - `squareKrylov_zero` — base case, definitional (rfl).
  - `squareKrylov_succ` — recurrence, definitional (rfl).
  - `squareKrylov_eq_pow_two` — bridge T_k = M^(2^k), one-line induction.

  **Out of scope (see module docstring).**
  - Layer 2 (correctness): Krylov-prefix ⊆ squared-Krylov span.
  - Layer 3 (complexity): O(n^ω) operation count — Mathlib-blocked.

  **Key insight.** The asymptotic Keller-Gehrig speed-up is *structural*:
  the same algebraic object (powers of M) is rearranged so log n
  matrix-matrix multiplications cover what n matrix-vector products would.
  The structural rearrangement formalises today; the quantitative gain
  cannot until Mathlib grows a complexity framework and a fast matmul.
-/
