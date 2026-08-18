import Proofs.Erdos85OrderSixtyFourSizeEightDefectClique
import Proofs.Erdos85MinimumSectorAssemblyInterface

/-! # Rank of normalized component averaging -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- The normalized component projection has trace equal to the number of
connected components. -/
theorem trace_defectComponentNormalizedProjection
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent] :
    Matrix.trace (defectComponentNormalizedProjection D) =
      Fintype.card D.ConnectedComponent := by
  letI (c : D.ConnectedComponent) : Fintype c.supp :=
    Fintype.ofFinite c.supp
  rw [Matrix.trace]
  change (∑ x : Fin 64,
      if D.connectedComponentMk x = D.connectedComponentMk x then
        ((D.connectedComponentMk x).supp.ncard : ℚ)⁻¹ else 0) = _
  simp only [if_pos]
  rw [sum_vertex_eq_sum_connectedComponent_supp D]
  calc
    (∑ c : D.ConnectedComponent, ∑ x : c.supp,
        ((D.connectedComponentMk x.1).supp.ncard : ℚ)⁻¹) =
      ∑ c : D.ConnectedComponent, ∑ _x : c.supp,
        (c.supp.ncard : ℚ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro x _
      rw [(SimpleGraph.ConnectedComponent.mem_supp_iff c x.1).mp x.2]
    _ = ∑ _c : D.ConnectedComponent, (1 : ℚ) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_const, nsmul_eq_mul]
      change (Fintype.card c.supp : ℚ) * (c.supp.ncard : ℚ)⁻¹ = 1
      rw [Set.fintypeCard_eq_ncard]
      have hp : c.supp.ncard ≠ 0 :=
        Nat.ne_of_gt c.nonempty_supp.ncard_pos
      field_simp
    _ = Fintype.card D.ConnectedComponent := by simp

/-- The range dimension of normalized component averaging is exactly the
number of components; its kernel has the complementary dimension. -/
theorem finrank_range_ker_defectComponentNormalizedProjection
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent] :
    Module.finrank ℚ (LinearMap.range
        (defectComponentNormalizedProjection D).toLin') =
        Fintype.card D.ConnectedComponent ∧
      Module.finrank ℚ (LinearMap.ker
        (defectComponentNormalizedProjection D).toLin') =
        64 - Fintype.card D.ConnectedComponent := by
  let P := defectComponentNormalizedProjection D
  have hPmatrix : P * P = P :=
    defectComponentNormalizedProjection_mul_self D
  have hPid : IsIdempotentElem P.toLin' := by
    simpa only [IsIdempotentElem, Module.End.mul_eq_comp,
      Matrix.toLin'_mul] using congrArg Matrix.toLin' hPmatrix
  have htraceLin : LinearMap.trace ℚ (Fin 64 → ℚ) P.toLin' =
      Fintype.card D.ConnectedComponent := by
    rw [Matrix.trace_toLin'_eq]
    exact trace_defectComponentNormalizedProjection D
  have hprojTrace : LinearMap.trace ℚ (Fin 64 → ℚ) P.toLin' =
      (Module.finrank ℚ (LinearMap.range P.toLin') : ℚ) :=
    (LinearMap.IsIdempotentElem.isProj_range P.toLin' hPid).trace
  have hrange : Module.finrank ℚ (LinearMap.range P.toLin') =
      Fintype.card D.ConnectedComponent := by
    exact_mod_cast (htraceLin.symm.trans hprojTrace).symm
  refine ⟨hrange, ?_⟩
  have hsum := LinearMap.finrank_range_add_finrank_ker P.toLin'
  have hamb : Module.finrank ℚ (Fin 64 → ℚ) = 64 := by simp
  rw [hrange, hamb] at hsum
  exact Nat.eq_sub_of_add_eq (by simpa [Nat.add_comm] using hsum)

/-- In the seven-component branch the residual sector has dimension 57. -/
theorem orderSixtyFour_residual_finrank_eq_fiftySeven_of_seven_components
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent]
    (hcount : Fintype.card D.ConnectedComponent = 7) :
    Module.finrank ℚ (LinearMap.ker
      (defectComponentNormalizedProjection D).toLin') = 57 := by
  have h := (finrank_range_ker_defectComponentNormalizedProjection
    D).2
  have harith : 64 - Fintype.card D.ConnectedComponent = 57 := by
    omega
  exact h.trans harith

end

end Erdos85
