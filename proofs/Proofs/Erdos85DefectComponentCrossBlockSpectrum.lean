import Proofs.Erdos85DefectComponentCrossBlockEquation
import Proofs.Erdos85OrderSixtyFourComponentGramIdentity

/-! # Spectral data carried across a defect-component cut

The diagonal block of the global second-order adjacency identity gives the
exact Gram operator of the exterior incidence block.  On the common
eigenspaces of the internal ambient and defect graphs this turns into a
scalar identity, complementing the exterior adjacency transfer.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

/-- **Cross-cut Gram identity.**  If `H` is the ambient adjacency inside a
defect component and `B` is its incidence with the exterior, then
`H² + BBᵀ = (q-1)I + J - D[c]`. -/
theorem binarySquare_regular_defectComponent_crossGram_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    let p : V → Prop := fun x ↦ x ∈ c.supp
    let H := (G.induce c.supp).adjMatrix ℤ
    let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
    let Dc := ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
    H * H + B * B.transpose =
      ((q : ℤ) - 1) • (1 : Matrix c.supp c.supp ℤ) +
        FriendshipTheoremOQ01.onesMatrix c.supp - Dc := by
  classical
  let D := secondOrderDefectGraph G
  let p : V → Prop := fun x ↦ x ∈ c.supp
  let H := (G.induce c.supp).adjMatrix ℤ
  let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
  let Dc := (D.induce c.supp).adjMatrix ℤ
  have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hblock := toBlock_sq_add_cross_eq_of_sq_eq
    (G.adjMatrix ℤ) (D.adjMatrix ℤ)
    (FriendshipTheoremOQ01.onesMatrix V) ((q : ℤ) - 1) hsq p
  have h11 : (G.adjMatrix ℤ).toBlock p p = H := by
    ext i j
    simp [H, p, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply]
  have h21 : (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) p = B.transpose := by
    ext i j
    simp [B, p, Matrix.toBlock_apply, Matrix.transpose_apply,
      SimpleGraph.adjMatrix_apply, G.adj_comm]
  have hD : (D.adjMatrix ℤ).toBlock p p = Dc := by
    ext i j
    simp [Dc, p, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply]
  rw [h11, h21, hD] at hblock
  exact hblock.trans (by
    congr 2)

/-- A zero-sum joint `(H,D[c])` eigenvector sees a scalar exterior Gram
operator.  The scalar `q-1-mu-theta²` is the exact exterior energy and hence
the obstruction to injectivity of the exterior transfer on that eigenline. -/
theorem binarySquare_regular_defectComponent_crossGram_jointEigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (f : c.supp → ℤ) (theta mu : ℤ)
    (hsum : ∑ x, f x = 0)
    (hH : ((G.induce c.supp).adjMatrix ℤ).mulVec f = theta • f)
    (hD : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ).mulVec f =
      mu • f) :
    let p : V → Prop := fun x ↦ x ∈ c.supp
    let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
    (B * B.transpose).mulVec f =
      ((q : ℤ) - 1 - mu - theta ^ 2) • f := by
  classical
  let p : V → Prop := fun x ↦ x ∈ c.supp
  let H := (G.induce c.supp).adjMatrix ℤ
  let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
  let Dc := ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix c.supp
  have hgram : H * H + B * B.transpose =
      ((q : ℤ) - 1) • (1 : Matrix c.supp c.supp ℤ) + J - Dc := by
    simpa [H, B, Dc, J, p] using
      binarySquare_regular_defectComponent_crossGram_eq G hfree hreg c
  have hJzero : J.mulVec f = 0 := by
    funext x
    simp [J, FriendshipTheoremOQ01.onesMatrix, Matrix.mulVec, dotProduct, hsum]
  have hv := congrArg (fun M : Matrix c.supp c.supp ℤ ↦ M.mulVec f) hgram
  change (B * B.transpose).mulVec f =
    ((q : ℤ) - 1 - mu - theta ^ 2) • f
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul, hH,
    Matrix.smul_mulVec, Matrix.one_mulVec, hJzero, hD] at hv
  ext x
  have hx := congrFun hv x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply] at hx ⊢
  ring_nf at hx ⊢
  omega

/-- **Non-saturated spectral pairing.**  Away from the saturated scalar
`q-1-mu-theta² = 0`, transposed exterior incidence maps a nonzero zero-sum
joint eigenvector to a nonzero exterior adjacency eigenvector with the
opposite ambient eigenvalue. -/
theorem binarySquare_regular_defectComponent_nonzero_exterior_eigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (f : c.supp → ℤ) (theta mu : ℤ)
    (hsum : ∑ x, f x = 0) (hf0 : f ≠ 0)
    (hH : ((G.induce c.supp).adjMatrix ℤ).mulVec f = theta • f)
    (hD : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ).mulVec f =
      mu • f)
    (hnonsat : (q : ℤ) - 1 - mu - theta ^ 2 ≠ 0) :
    let p : V → Prop := fun x ↦ x ∈ c.supp
    let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
    let C := (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
    B.transpose.mulVec f ≠ 0 ∧
      C.mulVec (B.transpose.mulVec f) = (-theta) • B.transpose.mulVec f := by
  classical
  let p : V → Prop := fun x ↦ x ∈ c.supp
  let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
  let C := (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
  have hgram := binarySquare_regular_defectComponent_crossGram_jointEigenvector
    G hfree hreg c f theta mu hsum hH hD
  have htransfer := binarySquare_regular_defectComponent_exterior_eigenvector_transfer
    G hfree hreg c f theta hsum hH
  change B.transpose.mulVec f ≠ 0 ∧
    C.mulVec (B.transpose.mulVec f) = (-theta) • B.transpose.mulVec f
  refine ⟨?_, by simpa [B, C, p] using htransfer⟩
  intro hzero
  have hleft : (B * B.transpose).mulVec f = 0 := by
    rw [← Matrix.mulVec_mulVec, hzero]
    simp
  have hscalar : ((q : ℤ) - 1 - mu - theta ^ 2) • f = 0 := by
    rw [← hgram]
    exact hleft
  apply hf0
  funext x
  have hx := congrFun hscalar x
  simp only [Pi.smul_apply, Pi.zero_apply] at hx
  exact (mul_eq_zero.mp hx).resolve_left hnonsat

/-- At order 64, the campaign-relevant internal eigenvalue `-2` has exterior
energy `3-mu`.  Hence `mu = 3` is the unique saturated value; every other
value produces a nonzero exterior eigenvector of eigenvalue `2`. -/
theorem orderSixtyFour_internalMinusTwo_nonzero_exterior_eigenvector_of_mu_ne_three
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (f : c.supp → ℤ) (mu : ℤ)
    (hsum : ∑ x, f x = 0) (hf0 : f ≠ 0)
    (hH : ((G.induce c.supp).adjMatrix ℤ).mulVec f = (-2 : ℤ) • f)
    (hD : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ).mulVec f =
      mu • f)
    (hmu : mu ≠ 3) :
    let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
    let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
    let C := (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
    B.transpose.mulVec f ≠ 0 ∧
      C.mulVec (B.transpose.mulVec f) = (2 : ℤ) • B.transpose.mulVec f := by
  have hnonsat : (8 : ℤ) - 1 - mu - (-2 : ℤ) ^ 2 ≠ 0 := by
    norm_num
    omega
  have h := binarySquare_regular_defectComponent_nonzero_exterior_eigenvector
    G hfree hreg c f (-2) mu hsum hf0 hH hD hnonsat
  norm_num at h ⊢
  exact h

end

#print axioms Erdos85.binarySquare_regular_defectComponent_crossGram_eq
#print axioms
  Erdos85.binarySquare_regular_defectComponent_crossGram_jointEigenvector
#print axioms
  Erdos85.binarySquare_regular_defectComponent_nonzero_exterior_eigenvector
#print axioms
  Erdos85.orderSixtyFour_internalMinusTwo_nonzero_exterior_eigenvector_of_mu_ne_three

end Erdos85
