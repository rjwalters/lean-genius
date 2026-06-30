/-
  Derangement Permutation Matrices: the matrix bridge for the 1/e law
  Open Question: derangements-oq-03-oq-03

  The "2D permutation-matrix" view of derangements.

  A uniformly random n×n permutation matrix is the permutation matrix `σ.permMatrix`
  of a uniformly random `σ ∈ Sym(n)`. Such a matrix is a *derangement matrix* — it has
  a zero diagonal — exactly when `σ` has no fixed point, i.e. `σ ∈ derangements (Fin n)`.

  This file builds the bridge between Mathlib's permutation-matrix API
  (`Equiv.Perm.permMatrix`, `Matrix.trace_permutation`) and the derangement combinatorics.
  It establishes — both pointwise (zero diagonal) and globally (zero trace) — that the
  derangement matrices are exactly the derangements, and that there are `numDerangements n`
  of them. Hence the probability that a uniformly random `n×n` permutation matrix is a
  derangement matrix is precisely `numDerangements n / n!`, the quantity whose sharp
  `1/e` convergence rate `|numDerangements n / n! - 1/e| ≤ 1/(n+1)!` is established in the
  companion analytic entry (gallery: `derangements-oq-03`, `Proofs.DerangementsOQ03`).

  This file is self-contained on Mathlib: no gallery dependencies.

  Main results:
  - `permMatrix_apply`:                entry `(σ.permMatrix ℝ) i j = if σ i = j then 1 else 0`
  - `permMatrix_diag`:                 diagonal `(σ.permMatrix ℝ) i i = if σ i = i then 1 else 0`
  - `permMatrix_diag_eq_zero_iff`:     `(σ.permMatrix ℝ) i i = 0 ↔ σ i ≠ i`
  - `hasZeroDiagonal_iff_mem_derangements`: zero diagonal ↔ `σ ∈ derangements (Fin n)`
  - `trace_permMatrix_eq_zero_iff`:    `trace (σ.permMatrix ℝ) = 0 ↔ σ ∈ derangements (Fin n)`
  - `zeroDiagonal_setOf_eq_derangements`: the derangement matrices are *exactly* the derangements
  - `card_derangement_permMatrices`:   their count is `numDerangements n`
  - `derangementMatrixProb`:           the probability `numDerangements n / n!`

  References:
  - Equiv.Perm.permMatrix, Matrix.trace_permutation (Mathlib)
  - Montmort (1708), Euler (1751): the derangement / 1-e law
-/

import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Tactic

open Equiv Equiv.Perm Matrix Finset Function
open scoped BigOperators

namespace DerangementsOQ03OQ03

variable {n : ℕ}

/-!
## Section I: The entry formula for a permutation matrix

For `σ ∈ Sym(Fin n)`, the permutation matrix `σ.permMatrix ℝ` has a single `1` in each
row, placed at column `σ i`. We record the entry formula and specialise it to the diagonal.
-/

/-- Entry formula: `(σ.permMatrix ℝ) i j = 1` iff `σ i = j`, else `0`. -/
theorem permMatrix_apply (σ : Perm (Fin n)) (i j : Fin n) :
    (σ.permMatrix ℝ) i j = if σ i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]

/-- Diagonal entry: `(σ.permMatrix ℝ) i i = 1` iff `i` is a fixed point of `σ`. -/
theorem permMatrix_diag (σ : Perm (Fin n)) (i : Fin n) :
    (σ.permMatrix ℝ) i i = if σ i = i then 1 else 0 :=
  permMatrix_apply σ i i

/-- A diagonal entry vanishes exactly at non-fixed points. -/
theorem permMatrix_diag_eq_zero_iff (σ : Perm (Fin n)) (i : Fin n) :
    (σ.permMatrix ℝ) i i = 0 ↔ σ i ≠ i := by
  rw [permMatrix_diag]
  by_cases h : σ i = i <;> simp [h]

/-!
## Section II: Derangement matrices are exactly the derangements

A *derangement matrix* is a permutation matrix with no `1` on the diagonal. We show this
geometric condition is equivalent to the combinatorial one (`σ` is a derangement), both
pointwise (zero diagonal) and globally (zero trace).
-/

/-- **Bridge lemma.** A permutation matrix has a zero diagonal iff the underlying
permutation is a derangement. -/
theorem hasZeroDiagonal_iff_mem_derangements (σ : Perm (Fin n)) :
    (∀ i, (σ.permMatrix ℝ) i i = 0) ↔ σ ∈ derangements (Fin n) := by
  simp only [permMatrix_diag_eq_zero_iff, derangements, Set.mem_setOf_eq]

/-- **Trace characterization.** Since the trace of a permutation matrix counts the fixed
points, it vanishes exactly when the permutation is a derangement. -/
theorem trace_permMatrix_eq_zero_iff (σ : Perm (Fin n)) :
    trace (σ.permMatrix ℝ) = 0 ↔ σ ∈ derangements (Fin n) := by
  rw [trace_permutation, Nat.cast_eq_zero, Set.ncard_eq_zero,
    mem_derangements_iff_fixedPoints_eq_empty]

/-- The set of zero-diagonal (derangement) permutation matrices is *exactly* the set of
derangements of `Fin n`. -/
theorem zeroDiagonal_setOf_eq_derangements :
    {σ : Perm (Fin n) | ∀ i, (σ.permMatrix ℝ) i i = 0} = derangements (Fin n) := by
  ext σ
  exact hasZeroDiagonal_iff_mem_derangements σ

/-!
## Section III: Counting derangement matrices and their probability

The number of derangement matrices of size `n` is `numDerangements n`, so the probability
that a uniformly random `n×n` permutation matrix is a derangement matrix is
`numDerangements n / n!`.  The sharp `1/e` convergence rate of this quantity is established
in the companion analytic entry `derangements-oq-03`.
-/

/-- The number of derangement permutation matrices on `Fin n` is `numDerangements n`. -/
theorem card_derangement_permMatrices :
    Fintype.card (derangements (Fin n)) = numDerangements n :=
  card_derangements_fin_eq_numDerangements

/-- There are at most `n!` derangements: they sit inside all `n!` permutations. -/
theorem numDerangements_le_factorial (n : ℕ) : numDerangements n ≤ n.factorial :=
  calc numDerangements n = Fintype.card (derangements (Fin n)) :=
        card_derangements_fin_eq_numDerangements.symm
    _ ≤ Fintype.card (Perm (Fin n)) := Fintype.card_subtype_le _
    _ = n.factorial := by rw [Fintype.card_perm, Fintype.card_fin]

/-- The probability that a uniformly random `n×n` permutation matrix is a derangement
matrix (zero diagonal), i.e. `numDerangements n / n!`. -/
noncomputable def derangementMatrixProb (n : ℕ) : ℝ :=
  (numDerangements n : ℝ) / (n.factorial : ℝ)

/-- The probability is a genuine probability: it lies in `[0, 1]`. -/
theorem derangementMatrixProb_mem_Icc (n : ℕ) : derangementMatrixProb n ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨by unfold derangementMatrixProb; positivity, ?_⟩
  rw [derangementMatrixProb, div_le_one (by exact_mod_cast n.factorial_pos)]
  exact_mod_cast numDerangements_le_factorial n

end DerangementsOQ03OQ03
