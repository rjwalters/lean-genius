import Proofs.Erdos85ComponentFactorization
import Proofs.Erdos85FrequencyPairEigenspace
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Eigenspaces decompose over connected components

For any finite graph, restriction to connected-component supports identifies a
global adjacency eigenspace with the dependent product of the corresponding
component eigenspaces.  Consequently its dimension is the sum of the component
dimensions.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Reindex a vertex function as a dependent family of functions on connected
component supports. -/
def connectedComponentFunctionLinearEquiv
    {K V : Type*} [Semiring K] (D : SimpleGraph V) :
    (V → K) ≃ₗ[K] ∀ c : D.ConnectedComponent, c.supp → K :=
  (LinearEquiv.piCongrLeft K
      (fun _ : Σ c : D.ConnectedComponent, c.supp => K)
      (vertexConnectedComponentEquiv D)).trans
    (LinearEquiv.piCurry K
      (fun (_c : D.ConnectedComponent) (_y : _c.supp) => K))

@[simp] theorem connectedComponentFunctionLinearEquiv_apply
    {K V : Type*} [Semiring K] (D : SimpleGraph V)
    (v : V → K) (c : D.ConnectedComponent) (y : c.supp) :
    connectedComponentFunctionLinearEquiv D v c y = v y.1 := by
  simp [connectedComponentFunctionLinearEquiv, LinearEquiv.piCongrLeft,
    LinearEquiv.piCongrLeft', Equiv.piCongrLeft',
    LinearEquiv.piCurry, Equiv.piCurry, Sigma.curry,
    vertexConnectedComponentEquiv]

/-- Restricting a global adjacency action to one component is the adjacency
action of the induced component graph. -/
theorem component_adjMatrix_mulVec_restrict
    {K V : Type*} [CommSemiring K] [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (c : D.ConnectedComponent) (v : V → K) (x : c.supp) :
    ((D.induce c.supp).adjMatrix K).mulVec (fun y => v y.1) x =
      (D.adjMatrix K).mulVec v x.1 := by
  classical
  rw [(D.induce c.supp).adjMatrix_mulVec_apply,
    D.adjMatrix_mulVec_apply]
  apply Finset.sum_bij (fun y _hy => y.1)
  · intro y hy
    have hy' : D.Adj x.1 y.1 := by
      simpa using ((D.induce c.supp).mem_neighborFinset x y).mp hy
    exact (D.mem_neighborFinset x.1 y.1).mpr hy'
  · intro y₁ hy₁ y₂ hy₂ heq
    exact Subtype.ext heq
  · intro y hy
    have hxy : D.Adj x.1 y := (D.mem_neighborFinset x.1 y).mp hy
    let z : c.supp := ⟨y, c.mem_supp_of_adj_mem_supp x.2 hxy⟩
    refine ⟨z, ?_, rfl⟩
    exact ((D.induce c.supp).mem_neighborFinset x z).mpr hxy
  · intro y _hy
    rfl

/-- The global adjacency eigenspace is the dependent product of the induced
component adjacency eigenspaces. -/
def connectedComponentEigenspaceLinearEquiv
    {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (μ : K) :
    defectEigenspace (D.adjMatrix K) μ ≃ₗ[K]
      ∀ c : D.ConnectedComponent,
        defectEigenspace ((D.induce c.supp).adjMatrix K) μ where
  toFun v c :=
    ⟨connectedComponentFunctionLinearEquiv D v.1 c, by
      rw [mem_defectEigenspace_iff]
      funext x
      have hx := congrFun (mem_defectEigenspace_iff.mp v.2) x.1
      calc
        ((D.induce c.supp).adjMatrix K).mulVec
            (connectedComponentFunctionLinearEquiv D v.1 c) x =
            ((D.induce c.supp).adjMatrix K).mulVec
              (fun y => v.1 y.1) x := by
                congr 1
                funext y
                rw [connectedComponentFunctionLinearEquiv_apply]
        _ = (D.adjMatrix K).mulVec v.1 x.1 :=
          component_adjMatrix_mulVec_restrict D c v.1 x
        _ = μ * v.1 x.1 := by
          simpa only [Pi.smul_apply, smul_eq_mul] using hx
        _ = (μ • connectedComponentFunctionLinearEquiv D v.1 c) x := by
          simp⟩
  invFun w :=
    ⟨(connectedComponentFunctionLinearEquiv D).symm (fun c => (w c).1), by
      rw [mem_defectEigenspace_iff]
      funext x
      let c := D.connectedComponentMk x
      let z : c.supp := ⟨x, rfl⟩
      have hc := congrFun
        ((connectedComponentFunctionLinearEquiv D).apply_symm_apply
          (fun c => (w c).1)) c
      have hz := congrFun (mem_defectEigenspace_iff.mp (w c).2) z
      let v₀ := (connectedComponentFunctionLinearEquiv D).symm
        (fun c => (w c).1)
      calc
        (D.adjMatrix K).mulVec v₀ x =
            ((D.induce c.supp).adjMatrix K).mulVec
              (fun y => v₀ y.1) z :=
          (component_adjMatrix_mulVec_restrict D c v₀ z).symm
        _ = ((D.induce c.supp).adjMatrix K).mulVec (w c).1 z := by
          congr 1
          funext y
          have hy := congrFun hc y
          simpa only [connectedComponentFunctionLinearEquiv_apply, v₀] using hy
        _ = μ * (w c).1 z := by
          simpa only [Pi.smul_apply, smul_eq_mul] using hz
        _ = μ * v₀ x := by
          have hz' := congrFun hc z
          simpa only [connectedComponentFunctionLinearEquiv_apply, v₀] using
            congrArg (fun a : K => μ * a) hz'.symm
        _ = (μ • v₀) x := by simp⟩
  left_inv v := by
    apply Subtype.ext
    exact (connectedComponentFunctionLinearEquiv D).symm_apply_apply v.1
  right_inv w := by
    funext c
    apply Subtype.ext
    have h := (connectedComponentFunctionLinearEquiv D).apply_symm_apply
      (fun c => (w c).1)
    exact congrFun h c
  map_add' u v := by
    funext c
    apply Subtype.ext
    exact congrFun
      ((connectedComponentFunctionLinearEquiv D).map_add u.1 v.1) c
  map_smul' a v := by
    funext c
    apply Subtype.ext
    exact congrFun
      ((connectedComponentFunctionLinearEquiv D).map_smul a v.1) c

/-- Exact eigenspace multiplicity sum over connected components. -/
theorem finrank_defectEigenspace_eq_sum_components
    {K V : Type*} [Field K] [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (μ : K) :
    Module.finrank K (defectEigenspace (D.adjMatrix K) μ) =
      ∑ c : D.ConnectedComponent,
        Module.finrank K
          (defectEigenspace ((D.induce c.supp).adjMatrix K) μ) := by
  rw [LinearEquiv.finrank_eq (connectedComponentEigenspaceLinearEquiv D μ),
    Module.finrank_pi_fintype]

end

end Erdos85
