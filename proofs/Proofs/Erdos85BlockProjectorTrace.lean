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

/-- After vertices are grouped by the connected components of `D`, the
diagonal `c`-block of the adjacency matrix of any graph `G` is precisely the
adjacency matrix induced by `G` on `c.supp`. -/
theorem sigmaDiagonalBlock_reindex_adjMatrix_eq_induce
    {V R : Type*} [Fintype V] [DecidableEq V] [Semiring R]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) :
    Matrix.sigmaDiagonalBlock
        ((G.adjMatrix R).reindex (vertexConnectedComponentEquiv D)
          (vertexConnectedComponentEquiv D)) c =
      (G.induce c.supp).adjMatrix R := by
  ext x y
  simp [Matrix.sigmaDiagonalBlock, Matrix.reindex_apply,
    vertexConnectedComponentEquiv, SimpleGraph.adjMatrix_apply]

/-- Graph-facing component trace ledger.  A block-diagonal family `P` indexed
by the connected components of `D` sees only the owner matrices induced by
`G` on those same components. -/
theorem trace_reindex_adjMatrix_mul_componentBlockDiagonal
    {V R : Type*} [Fintype V] [DecidableEq V] [CommSemiring R]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    [∀ c : D.ConnectedComponent, Fintype c.supp]
    (P : ∀ c : D.ConnectedComponent, Matrix c.supp c.supp R) :
    Matrix.trace
        ((G.adjMatrix R).reindex (vertexConnectedComponentEquiv D)
            (vertexConnectedComponentEquiv D) *
          Matrix.blockDiagonal' P) =
      ∑ c : D.ConnectedComponent,
        Matrix.trace ((G.induce c.supp).adjMatrix R * P c) := by
  rw [Matrix.trace_mul_blockDiagonal']
  apply Finset.sum_congr rfl
  intro c _
  rw [sigmaDiagonalBlock_reindex_adjMatrix_eq_induce G D c]

/-- A componentwise polynomial in the induced defect adjacency matrices,
assembled in the canonical connected-component coordinates.  Allowing the
polynomial to depend on the component accommodates unequal local spectra. -/
def componentPolynomialBlockDiagonal
    {V R : Type*} [Fintype V] [DecidableEq V] [CommSemiring R]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    [∀ c : D.ConnectedComponent, Fintype c.supp]
    (p : D.ConnectedComponent → Polynomial R) :
    Matrix (Σ c : D.ConnectedComponent, c.supp)
      (Σ c : D.ConnectedComponent, c.supp) R :=
  Matrix.blockDiagonal' fun c =>
    Polynomial.aeval ((D.induce c.supp).adjMatrix R) (p c)

/-- Intrinsic componentwise polynomial trace ledger.  This is the exact
algebraic interface used when each `p c` is chosen as the spectral projector
onto a specified local defect eigenvalue. -/
theorem trace_reindex_adjMatrix_mul_componentPolynomialBlockDiagonal
    {V R : Type*} [Fintype V] [DecidableEq V] [CommSemiring R]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    [∀ c : D.ConnectedComponent, Fintype c.supp]
    (p : D.ConnectedComponent → Polynomial R) :
    Matrix.trace
        ((G.adjMatrix R).reindex (vertexConnectedComponentEquiv D)
            (vertexConnectedComponentEquiv D) *
          componentPolynomialBlockDiagonal D p) =
      ∑ c : D.ConnectedComponent,
        Matrix.trace
          ((G.induce c.supp).adjMatrix R *
            Polynomial.aeval ((D.induce c.supp).adjMatrix R) (p c)) := by
  exact trace_reindex_adjMatrix_mul_componentBlockDiagonal G D
    (fun c => Polynomial.aeval ((D.induce c.supp).adjMatrix R) (p c))

end

end Erdos85
