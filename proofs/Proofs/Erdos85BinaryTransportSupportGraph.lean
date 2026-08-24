import Proofs.Erdos85F2MatrixSupportGraph
import Proofs.Erdos85CubicDiagonalParity
import Proofs.Erdos85EvenExcessOneDefectKernel

/-!
# The binary transport support graph

For an even-regular graph with adjacency matrix `A` over F₂, the Baer audit
uses the transport matrix `H = A²(A+I)`.  Here it is shown symmetric,
zero-diagonal, and zero-row-sum, then realized as an honest Eulerian simple
graph through `f2MatrixSupportGraph`.
-/

open SimpleGraph

namespace Erdos85

/-- The binary transport matrix `A²(A+I)`. -/
def binaryTransportMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V (ZMod 2) :=
  let A := G.adjMatrix (ZMod 2)
  A * A * (A + 1)

theorem binaryTransportMatrix_eq_cube_add_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    binaryTransportMatrix G =
      (G.adjMatrix (ZMod 2)) ^ 3 + (G.adjMatrix (ZMod 2)) ^ 2 := by
  simp [binaryTransportMatrix, pow_succ, Matrix.mul_add, mul_assoc]

/-- The transport matrix is symmetric because it is a polynomial in the
symmetric adjacency matrix. -/
theorem binaryTransportMatrix_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    binaryTransportMatrix G x y = binaryTransportMatrix G y x := by
  have hsymm : (binaryTransportMatrix G).IsSymm := by
    rw [binaryTransportMatrix_eq_cube_add_sq]
    exact (G.isSymm_adjMatrix.pow 3).add (G.isSymm_adjMatrix.pow 2)
  simpa [Matrix.transpose_apply] using congr_fun₂ hsymm.eq y x

/-- At even regular degree the transport diagonal vanishes. -/
theorem binaryTransportMatrix_diag_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, G.degree v = q) (x : V) :
    binaryTransportMatrix G x x = 0 := by
  let A₂ := G.adjMatrix (ZMod 2)
  let Aℤ := G.adjMatrix ℤ
  have hcubeEven := even_adjMatrix_cube_apply_self G x
  have hcubeCast :
      (((Aℤ * Aℤ * Aℤ) x x : ℤ) : ZMod 2) = (A₂ * A₂ * A₂) x x := by
    let f := Int.castRingHom (ZMod 2)
    have hadjMap : Aℤ.map f = A₂ := by
      ext u v
      simp [Aℤ, A₂, Matrix.map_apply, SimpleGraph.adjMatrix_apply]
    have hcubeMap : (Aℤ * Aℤ * Aℤ).map f = A₂ * A₂ * A₂ := by
      rw [Matrix.map_mul, Matrix.map_mul, hadjMap]
    exact congr_fun₂ hcubeMap x x
  have hcubeZero : (A₂ * A₂ * A₂) x x = 0 := by
    obtain ⟨k, hk⟩ := hcubeEven
    rw [← hcubeCast, hk]
    push_cast
    exact zmodTwo_add_self _
  have hsquareZero : (A₂ * A₂) x x = 0 := by
    rw [SimpleGraph.adjMatrix_mul_self_apply_self, hreg x]
    obtain ⟨k, hk⟩ := hq
    rw [hk]
    push_cast
    exact zmodTwo_add_self _
  rw [binaryTransportMatrix_eq_cube_add_sq]
  have hcubePow : (G.adjMatrix (ZMod 2) ^ 3) x x = 0 := by
    simpa [A₂, pow_succ, pow_two, mul_assoc] using hcubeZero
  have hsquarePow : (G.adjMatrix (ZMod 2) ^ 2) x x = 0 := by
    simpa [A₂, pow_two] using hsquareZero
  rw [Matrix.add_apply, hcubePow, hsquarePow, add_zero]

/-- At even regular degree, `A²(A+I)` kills the all-ones vector. -/
theorem binaryTransportMatrix_mulVec_one_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, G.degree v = q) :
    (binaryTransportMatrix G).mulVec (fun _ => 1) = 0 := by
  let A := G.adjMatrix (ZMod 2)
  have hA := adjMatrix_zmodTwo_mulVec_ones_eq_zero G hq hreg
  change (A * A * (A + 1)).mulVec (fun _ => 1) = 0
  have hplus : (A + 1).mulVec (fun _ => 1) = (fun _ => 1) := by
    rw [Matrix.add_mulVec, hA, Matrix.one_mulVec, zero_add]
  rw [← Matrix.mulVec_mulVec, hplus, ← Matrix.mulVec_mulVec, hA,
    Matrix.mulVec_zero]

/-- The simple support graph of the binary transport matrix. -/
def binaryTransportSupportGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, G.degree v = q) : SimpleGraph V :=
  f2MatrixSupportGraph (binaryTransportMatrix G)
    (binaryTransportMatrix_symm G)
    (binaryTransportMatrix_diag_eq_zero G hq hreg)

instance binaryTransportSupportGraph_decidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, G.degree v = q) :
    DecidableRel (binaryTransportSupportGraph G hq hreg).Adj := by
  unfold binaryTransportSupportGraph
  infer_instance

/-- The transport support graph is Eulerian. -/
theorem binaryTransportSupportGraph_even_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, G.degree v = q) (v : V) :
    Even ((binaryTransportSupportGraph G hq hreg).degree v) := by
  exact f2MatrixSupportGraph_even_degree_of_mulVec_one_eq_zero
    (binaryTransportMatrix G) (binaryTransportMatrix_symm G)
    (binaryTransportMatrix_diag_eq_zero G hq hreg)
    (binaryTransportMatrix_mulVec_one_eq_zero G hq hreg) v

end Erdos85

#print axioms Erdos85.binaryTransportMatrix_diag_eq_zero
#print axioms Erdos85.binaryTransportMatrix_mulVec_one_eq_zero
#print axioms Erdos85.binaryTransportSupportGraph_even_degree
