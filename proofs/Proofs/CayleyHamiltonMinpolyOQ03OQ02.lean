/-
  Squared-Krylov Sequence — Structural + Correctness Layers of the
  Keller-Gehrig Algorithm
  (cayley-hamilton-minpoly-oq-03-oq-02)

  Question: Can the O(n^ω) Keller-Gehrig algorithm (1985) be formalised,
  extending the Krylov framework (CayleyHamiltonMinpolyOQ03.lean, naive
  O(n³)) to subcubic complexity?

  This file commits to **Layers 1 and 2** of the three-layer decomposition
  (see research/problems/cayley-hamilton-minpoly-oq-03-oq-02/problem.md):

  * **Layer 1 (structural).** Define the squared-Krylov sequence

        T_k := M^(2^k)

    computed by repeated squaring (T_{k+1} = T_k · T_k), and prove the
    bridge `T_k = M^(2^k)`. This is the algebraic fact that powers the
    asymptotic Keller-Gehrig speed-up: ⌈log₂ j⌉ matrix multiplications
    cover every Krylov power M^j.

  * **Layer 2 (correctness).** Every matrix power M^j is recoverable as a
    *product* of squared-Krylov matrices indexed by the set bits of j:

        M^j = ∏_{i ∈ bitIndices j} T_i.

    Hence the Keller-Gehrig pass — `⌈log₂ j⌉ + 1` matrix squarings
    followed by `popcount(j)` matrix multiplications — yields any Krylov
    power M^j without ever traversing the n-step Krylov ladder.

  The third layer is explicitly *out of scope*:

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
  - Mathlib: `Data.Nat.BitIndices` (Peter Nelson) — provides
    `Nat.bitIndices` and `Nat.twoPowSum_bitIndices`, the binary expansion
    identity that powers the Layer 2 bridge.

  See also:
  - `CayleyHamiltonMinpolyOQ03.lean` — naive O(n³) Krylov for μ_M.
  - `CayleyHamiltonMinpolyOQ03OQ01.lean` — vector-specific Krylov (sibling).
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Data.Nat.BitIndices
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

-- ============================================================
-- Layer 2: Correctness — Krylov powers via binary expansion
-- ============================================================

/-- The **squared-Krylov product** for a natural number `j`: the product of
    `squareKrylov M i` over the set bits of `j`. This is the matrix the
    Keller-Gehrig outer loop produces after `⌈log₂ j⌉` squarings and
    `popcount(j)` multiplications.

    Definitionally: `squareKrylovProd M j = ∏ i ∈ bitIndices j, T_i`. -/
def squareKrylovProd (M : Matrix (Fin n) (Fin n) K) (j : ℕ) :
    Matrix (Fin n) (Fin n) K :=
  (j.bitIndices.map (squareKrylov M)).prod

/-- Powers of a single element commute, so `List.prod` of `M^(f i)` over a
    list collapses to a single power of `M`. -/
private theorem prod_pow_of_list (M : Matrix (Fin n) (Fin n) K) (L : List ℕ) :
    (L.map (fun i => M ^ (2 ^ i))).prod = M ^ ((L.map (fun i => 2 ^ i)).sum) := by
  induction L with
  | nil => simp
  | cons a L ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add, ih]

/-- **Layer 2 (correctness).** Every matrix power `M^j` is the product of
    squared-Krylov matrices indexed by the set bits of `j`:

        M^j = ∏ i ∈ bitIndices j, T_i.

    This is the algebraic content of the Keller-Gehrig outer loop: once the
    squared-Krylov sequence `T_0, T_1, …` is in hand (Layer 1), any Krylov
    power `M^j` is recovered by one matrix product per set bit of `j`. For
    `j < n`, this is at most `⌈log₂ n⌉` multiplications, replacing the
    `n` matrix-vector products of the naive Krylov method (OQ-03).

    The proof factors through Mathlib's `Nat.twoPowSum_bitIndices`
    (the binary-expansion identity `∑ i ∈ bitIndices j, 2^i = j`),
    the Layer 1 bridge `squareKrylov M i = M^(2^i)`, and the fact that
    powers of a single element commute (giving
    `∏ M^(2^i) = M^(∑ 2^i)`). -/
theorem squareKrylovProd_eq_pow (M : Matrix (Fin n) (Fin n) K) (j : ℕ) :
    squareKrylovProd M j = M ^ j := by
  unfold squareKrylovProd
  have hmap :
      j.bitIndices.map (squareKrylov M) = j.bitIndices.map (fun i => M ^ (2 ^ i)) :=
    List.map_congr_left (fun i _ => squareKrylov_eq_pow_two M i)
  rw [hmap, prod_pow_of_list, Nat.twoPowSum_bitIndices]

/-- **Sanity check** at `j = 0`: the empty product is the identity matrix,
    consistent with `M^0 = 1`. -/
@[simp]
theorem squareKrylovProd_zero (M : Matrix (Fin n) (Fin n) K) :
    squareKrylovProd M 0 = 1 := by
  rw [squareKrylovProd_eq_pow, pow_zero]

/-- **Sanity check** at `j = 1`: a one-element product yields `T_0 = M`. -/
theorem squareKrylovProd_one (M : Matrix (Fin n) (Fin n) K) :
    squareKrylovProd M 1 = M := by
  rw [squareKrylovProd_eq_pow, pow_one]

/-- **Sanity check** at `j = 2^k`: the bit-pattern is a single bit at
    position `k`, so the product is exactly `T_k = M^(2^k)`. -/
theorem squareKrylovProd_two_pow (M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    squareKrylovProd M (2 ^ k) = squareKrylov M k := by
  rw [squareKrylovProd_eq_pow, squareKrylov_eq_pow_two]

-- ============================================================
-- Layer 2 vector form: Krylov vectors via squared-Krylov
-- ============================================================

/-- **Vector-level Layer 2.** Every Krylov vector `M^j · v` is the result of
    applying the squared-Krylov product `squareKrylovProd M j` to `v`. This
    is the operationally accurate form of Layer 2: the algorithm produces
    each Krylov vector by applying a single matrix (the squared-Krylov
    product, built from `popcount(j)` matrix multiplications of the squared
    sequence) to `v`. -/
theorem squareKrylovProd_mulVec (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (j : ℕ) :
    (squareKrylovProd M j).mulVec v = (M ^ j).mulVec v := by
  rw [squareKrylovProd_eq_pow]

/-- **Krylov reachability.** Every Krylov vector `M^j · v` lies in the range
    of `squareKrylovProd M j` viewed as a matrix-vector map. This is the
    span-style restatement of the vector-level Layer 2 bridge: any vector
    the naive Krylov ladder produces is reachable through the
    `popcount(j)`-multiplication squared-Krylov product map. -/
theorem krylov_in_squareKrylov_range (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (j : ℕ) :
    ∃ w : Fin n → K, (squareKrylovProd M j).mulVec w = (M ^ j).mulVec v :=
  ⟨v, squareKrylovProd_mulVec M v j⟩

end MinpolyComplexity.SubcubicKrylov

/-
  ## Summary

  **Problem (Layers 1 + 2 of cayley-hamilton-minpoly-oq-03-oq-02).**
  Define the squared-Krylov sequence T_k := M^(2^k) via repeated squaring,
  prove the bridge to ordinary matrix exponentiation, and lift the bridge
  to a binary-expansion product formula recovering every Krylov power M^j.

  **Status.** Complete formalization of Layers 1 + 2 + vector-level
  corollaries. 9 theorems (3 Layer 1 + 4 Layer 2 matrix-level + 2
  Layer 2 vector-level), 0 sorries, 0 axioms.

  **Layer 1 (structural, 3 theorems).**
  - `squareKrylov_zero` — base case, definitional (rfl).
  - `squareKrylov_succ` — recurrence, definitional (rfl).
  - `squareKrylov_eq_pow_two` — bridge T_k = M^(2^k), one-line induction.

  **Layer 2 (correctness — matrix level, 4 theorems + 1 helper).**
  - `squareKrylovProd` — definition: product of T_i over set bits of j.
  - `prod_pow_of_list` — helper: `∏ M^(2^i) = M^(∑ 2^i)` over a list.
  - `squareKrylovProd_eq_pow` — bridge M^j = ∏_{i ∈ bitIndices j} T_i.
  - `squareKrylovProd_zero` — sanity check (empty product = 1).
  - `squareKrylovProd_one` — sanity check (single T_0 = M).
  - `squareKrylovProd_two_pow` — sanity check (T_k recovered from 2^k).

  **Layer 2 vector form (S4 addition, 2 theorems).**
  - `squareKrylovProd_mulVec` — vector corollary: `(squareKrylovProd M j).mulVec v = (M^j).mulVec v`.
  - `krylov_in_squareKrylov_range` — reachability: every Krylov vector lies in the image of the squared-Krylov product matrix-vector map.

  **Out of scope (see module docstring).**
  - Layer 3 (complexity): O(n^ω) operation count — Mathlib-blocked.

  **Key insight.** The asymptotic Keller-Gehrig speed-up is *structural*:
  the same algebraic object (powers of M) is rearranged so log n
  matrix-matrix multiplications cover what n matrix-vector products would.
  The structural rearrangement (Layer 1) and the correctness bridge
  (Layer 2) formalise today; the quantitative gain (Layer 3) cannot
  until Mathlib grows a complexity framework and a fast matmul.

  **Layer 2 proof sketch.** Each squared-Krylov matrix is `T_i = M^(2^i)`
  (Layer 1). The product over the set bits of j thus equals `M^(∑ 2^i)`
  (powers of a single matrix commute, so the list product collapses).
  Mathlib's `Nat.twoPowSum_bitIndices` then identifies that sum as j
  itself — the binary expansion of j is exactly the indicator vector
  of its set bits. End-to-end, the proof is three rewrites against
  `squareKrylov_eq_pow_two`, the `prod_pow_of_list` helper, and
  `Nat.twoPowSum_bitIndices`.
-/
