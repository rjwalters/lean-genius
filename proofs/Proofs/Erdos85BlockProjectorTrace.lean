import Proofs.Erdos85ComponentFactorization

/-! # Trace against a block-diagonal projector

Only the diagonal blocks of an arbitrary operator contribute to its trace
after multiplication by a block-diagonal operator.  This elementary identity
is the basis-free bookkeeping step behind the componentwise `τ` ledgers.
-/

namespace Erdos85

noncomputable section

/-- The diagonal block of a matrix indexed by a dependent disjoint union. -/
def Matrix.sigmaDiagonalBlock
    {C R : Type*} {V : C → Type*}
    (A : Matrix (Σ c, V c) (Σ c, V c) R) (c : C) :
    Matrix (V c) (V c) R := fun x y => A ⟨c, x⟩ ⟨c, y⟩

/-- Multiplying by a dependent block diagonal matrix discards all off-block
parts of the other factor from the trace. -/
theorem Matrix.trace_mul_blockDiagonal'
    {C R : Type*} [Fintype C] [DecidableEq C]
    {V : C → Type*} [∀ c, Fintype (V c)] [∀ c, DecidableEq (V c)]
    [CommSemiring R]
    (A : Matrix (Σ c, V c) (Σ c, V c) R)
    (P : ∀ c, Matrix (V c) (V c) R) :
    Matrix.trace (A * Matrix.blockDiagonal' P) =
      ∑ c, Matrix.trace (Matrix.sigmaDiagonalBlock A c * P c) := by
  simp only [Matrix.trace, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro x _
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single c]
  · simp [Matrix.blockDiagonal'_apply_eq, Matrix.sigmaDiagonalBlock]
  · intro c' _ hne
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ hne]
  · simp

/-- Equivalent right-multiplication form, useful when cyclicity has already
placed the block-diagonal projector first. -/
theorem Matrix.trace_blockDiagonal'_mul
    {C R : Type*} [Fintype C] [DecidableEq C]
    {V : C → Type*} [∀ c, Fintype (V c)] [∀ c, DecidableEq (V c)]
    [CommRing R]
    (P : ∀ c, Matrix (V c) (V c) R)
    (A : Matrix (Σ c, V c) (Σ c, V c) R) :
    Matrix.trace (Matrix.blockDiagonal' P * A) =
      ∑ c, Matrix.trace (P c * Matrix.sigmaDiagonalBlock A c) := by
  rw [Matrix.trace_mul_comm]
  rw [Matrix.trace_mul_blockDiagonal']
  apply Finset.sum_congr rfl
  intro c _
  exact Matrix.trace_mul_comm _ _

end

end Erdos85
