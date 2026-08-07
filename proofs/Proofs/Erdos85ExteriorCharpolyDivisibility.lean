import Proofs.Erdos85OneTwentyThreeHardSector
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Characteristic factors of the exterior defect operator

The minimum-layer exterior is a union of whole parent-defect components.
Consequently its adjacency matrix is a diagonal block of the global defect
matrix, and its characteristic polynomial divides the global one.  This is
the bridge from a hard-sector factor to one of the global cycle Chebyshev
factors.
-/

namespace Erdos85

noncomputable section

open Matrix

/-- An invariant range of an idempotent contributes a characteristic
factor of the ambient endomorphism. -/
theorem charpoly_restrict_range_dvd_of_idempotent
    {E : Type*} [AddCommGroup E] [Module ℚ E]
    [FiniteDimensional ℚ E]
    (T Q : E →ₗ[ℚ] E) (hQ : IsIdempotentElem Q)
    (hcomm : T * Q = Q * T) :
    let hR : ∀ x ∈ LinearMap.range Q, T x ∈ LinearMap.range Q :=
      mapsTo_range_of_commute (E := E) T Q hcomm
    (T.restrict hR).charpoly ∣ T.charpoly := by
  dsimp only
  let R := LinearMap.range Q
  let W := LinearMap.ker Q
  let hR := mapsTo_range_of_commute T Q hcomm
  let hW := mapsTo_ker_of_commute T Q hcomm
  have hfactor := charpoly_eq_mul_restrict_of_isCompl T R W
    (LinearMap.IsIdempotentElem.isCompl hQ) hR hW
  rw [hfactor]
  exact dvd_mul_right _ _

/-- Matrix form of `charpoly_restrict_range_dvd_of_idempotent`. -/
theorem charpoly_matrix_restrict_range_dvd
    {X : Type*} [Fintype X] [DecidableEq X]
    (T Q : Matrix X X ℚ) (hQ : Q * Q = Q)
    (hcomm : T * Q = Q * T) :
    let TL := T.toLin'
    let QL := Q.toLin'
    let hc : TL * QL = QL * TL := by
      simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
        congrArg Matrix.toLin' hcomm
    let hR : ∀ x ∈ LinearMap.range QL, TL x ∈ LinearMap.range QL :=
      mapsTo_range_of_commute TL QL hc
    (TL.restrict hR).charpoly ∣ T.charpoly := by
  dsimp only
  have hQL : IsIdempotentElem Q.toLin' := by
    simpa only [IsIdempotentElem, Module.End.mul_eq_comp,
      Matrix.toLin'_mul] using congrArg Matrix.toLin' hQ
  have hc : T.toLin' * Q.toLin' = Q.toLin' * T.toLin' := by
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hcomm
  have hdvd := charpoly_restrict_range_dvd_of_idempotent
    T.toLin' Q.toLin' hQL hc
  simpa [Matrix.charpoly_toLin'] using hdvd

/-- The characteristic polynomial of a closed principal block divides the
characteristic polynomial of the full matrix. -/
theorem charpoly_toSquareBlockProp_dvd_of_zero_cross
    {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]
    (M : Matrix I I K) (p : I → Prop) [DecidablePred p]
    [Fintype {i // p i}] [DecidableEq {i // p i}]
    [Fintype {i // ¬p i}] [DecidableEq {i // ¬p i}]
    (hzero : ∀ i, ¬p i → ∀ j, p j → M i j = 0) :
    (Matrix.toSquareBlockProp M p).charpoly ∣ M.charpoly := by
  let e : I ≃ ({i // p i} ⊕ {i // ¬p i}) := (Equiv.sumCompl p).symm
  let A := Matrix.toBlock M p p
  let B := Matrix.toBlock M p (fun i => ¬p i)
  let C := Matrix.toBlock M (fun i => ¬p i) p
  let D := Matrix.toBlock M (fun i => ¬p i) (fun i => ¬p i)
  have hC : C = 0 := by
    ext i j
    exact hzero i.1 i.2 j.1 j.2
  have hreindex : Matrix.reindex e e M = Matrix.fromBlocks A B C D := by
    ext i j
    cases i <;> cases j <;>
      simp [e, A, B, C, D, Matrix.reindex_apply]
  have hfactor : M.charpoly = A.charpoly * D.charpoly := by
    calc
      M.charpoly = (Matrix.reindex e e M).charpoly :=
        (Matrix.charpoly_reindex e M).symm
      _ = (Matrix.fromBlocks A B C D).charpoly := by rw [hreindex]
      _ = (Matrix.fromBlocks A B 0 D).charpoly := by rw [hC]
      _ = A.charpoly * D.charpoly := by
        simpa using Matrix.charpoly_fromBlocks_zero₂₁ A B D
  rw [hfactor]
  exact dvd_mul_right _ _

/-- The parent-defect matrix induced on the minimum-layer exterior has
characteristic polynomial dividing that of the full parent defect matrix. -/
theorem minimumLayerExterior_defect_charpoly_dvd_global
    {V K : Type*} [Fintype V] [DecidableEq V] [CommRing K]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent)
    [DecidableEq (minimumLayerExteriorVertex D c₀)] :
    ((D.comap (fun z : minimumLayerExteriorVertex D c₀ => z.1)).adjMatrix K).charpoly ∣
      (D.adjMatrix K).charpoly := by
  classical
  let U := minimumLayerImageFinset D c₀
  let p : V → Prop := fun v => v ∉ U
  have hzero : ∀ i, ¬p i → ∀ j, p j → (D.adjMatrix K) i j = 0 := by
    intro i hi j hj
    have hnot : ¬D.Adj i j := by
      intro hij
      have hout := minimumLayerExterior_closed_under_reachable D c₀
        (⟨j, hj⟩ : minimumLayerExteriorVertex D c₀) hij.symm.reachable
      exact hi hout
    simp [SimpleGraph.adjMatrix_apply, hnot]
  have hdvd := @charpoly_toSquareBlockProp_dvd_of_zero_cross
    V K _ _ _ (D.adjMatrix K) p _
      (inferInstance : Fintype (minimumLayerExteriorVertex D c₀))
      (inferInstance : DecidableEq (minimumLayerExteriorVertex D c₀))
      (inferInstance : Fintype {i // ¬p i})
      (inferInstance : DecidableEq {i // ¬p i}) hzero
  exact hdvd

/-- The characteristic polynomial on any invariant idempotent sector of
the exterior parent-defect operator divides the global parent-defect
characteristic polynomial. -/
theorem minimumLayerExterior_hardSector_charpoly_dvd_global
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent)
    [DecidableEq (minimumLayerExteriorVertex D c₀)]
    (Q : Matrix (minimumLayerExteriorVertex D c₀)
      (minimumLayerExteriorVertex D c₀) ℚ)
    (hQ : Q * Q = Q)
    (hcomm :
      (D.comap (fun z : minimumLayerExteriorVertex D c₀ => z.1)).adjMatrix ℚ * Q =
        Q * (D.comap (fun z : minimumLayerExteriorVertex D c₀ => z.1)).adjMatrix ℚ) :
    let P := (D.comap
      (fun z : minimumLayerExteriorVertex D c₀ => z.1)).adjMatrix ℚ
    let PL := P.toLin'
    let QL := Q.toLin'
    let hc : PL * QL = QL * PL := by
      simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
        congrArg Matrix.toLin' hcomm
    let hR : ∀ x ∈ LinearMap.range QL, PL x ∈ LinearMap.range QL :=
      mapsTo_range_of_commute PL QL hc
    (PL.restrict hR).charpoly ∣ (D.adjMatrix ℚ).charpoly := by
  dsimp only
  let P := (D.comap
    (fun z : minimumLayerExteriorVertex D c₀ => z.1)).adjMatrix ℚ
  have hsector := charpoly_matrix_restrict_range_dvd P Q hQ hcomm
  have hexterior := minimumLayerExterior_defect_charpoly_dvd_global
    (K := ℚ) D c₀
  exact dvd_trans hsector hexterior

end

end Erdos85
