import Proofs.Erdos85OrderSixtyFourComponentMeanZero

/-! # Splitting the residual sector over connected components -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Reindex a function on the 64 vertices as a dependent family of functions
on connected-component supports. -/
def componentFunctionLinearEquiv
    (D : SimpleGraph (Fin 64)) :
    (Fin 64 → ℚ) ≃ₗ[ℚ]
      ∀ c : D.ConnectedComponent, c.supp → ℚ :=
  (LinearEquiv.piCongrLeft ℚ
      (fun _ : Σ c : D.ConnectedComponent, c.supp => ℚ)
      (vertexConnectedComponentEquiv D)).trans
    (LinearEquiv.piCurry ℚ
      (fun (_c : D.ConnectedComponent) (_y : _c.supp) => ℚ))

@[simp] theorem componentFunctionLinearEquiv_apply
    (D : SimpleGraph (Fin 64)) (v : Fin 64 → ℚ)
    (c : D.ConnectedComponent) (y : c.supp) :
    componentFunctionLinearEquiv D v c y = v y.1 := by
  simp [componentFunctionLinearEquiv, LinearEquiv.piCongrLeft,
    LinearEquiv.piCongrLeft', Equiv.piCongrLeft',
    LinearEquiv.piCurry, Equiv.piCurry, Sigma.curry,
    vertexConnectedComponentEquiv]

/-- The dependent product of the mean-zero spaces of all connected
components. -/
abbrev componentMeanZeroFamily
    (D : SimpleGraph (Fin 64))
    [∀ c : D.ConnectedComponent, Fintype c.supp] :=
  ∀ c : D.ConnectedComponent,
    LinearMap.ker (coordinateSumLinearMap c.supp)

/-- The global residual sector is linearly equivalent to the dependent
product of the componentwise mean-zero sectors. -/
def residualComponentMeanZeroLinearEquiv
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent]
    [∀ c : D.ConnectedComponent, Fintype c.supp] :
    LinearMap.ker (defectComponentNormalizedProjection D).toLin' ≃ₗ[ℚ]
      componentMeanZeroFamily D where
  toFun v c :=
    ⟨componentFunctionLinearEquiv D v.1 c, by
      apply LinearMap.mem_ker.mpr
      change ∑ y : c.supp, componentFunctionLinearEquiv D v.1 c y = 0
      simpa only [componentFunctionLinearEquiv_apply] using
        (mem_ker_defectComponentNormalizedProjection_iff_component_sum_zero
          D v.1).mp v.2 c⟩
  invFun w :=
    ⟨(componentFunctionLinearEquiv D).symm (fun c => (w c).1), by
      apply (mem_ker_defectComponentNormalizedProjection_iff_component_sum_zero
        D _).mpr
      intro c
      have hinv := (componentFunctionLinearEquiv D).apply_symm_apply
        (fun c => (w c).1)
      have hc : componentFunctionLinearEquiv D
          ((componentFunctionLinearEquiv D).symm (fun c => (w c).1)) c =
          (w c).1 := congrFun hinv c
      calc
        (∑ y : c.supp,
            (componentFunctionLinearEquiv D).symm
              (fun c => (w c).1) y.1) =
            ∑ y : c.supp,
              componentFunctionLinearEquiv D
                ((componentFunctionLinearEquiv D).symm
                  (fun c => (w c).1)) c y := by
              apply Finset.sum_congr rfl
              intro y _
              rw [componentFunctionLinearEquiv_apply]
        _ = ∑ y : c.supp, (w c).1 y := by rw [hc]
        _ = 0 := (w c).2⟩
  left_inv v := by
    apply Subtype.ext
    exact (componentFunctionLinearEquiv D).symm_apply_apply v.1
  right_inv w := by
    funext c
    apply Subtype.ext
    have h := (componentFunctionLinearEquiv D).apply_symm_apply
      (fun c => (w c).1)
    exact congrFun h c
  map_add' u v := by
    funext c
    apply Subtype.ext
    exact congrFun ((componentFunctionLinearEquiv D).map_add u.1 v.1) c
  map_smul' a v := by
    funext c
    apply Subtype.ext
    exact congrFun ((componentFunctionLinearEquiv D).map_smul a v.1) c

end

end Erdos85
