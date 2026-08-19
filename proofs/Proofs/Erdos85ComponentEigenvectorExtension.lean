import Proofs.Erdos85OrderSixtyFourLocalizedEigenvector

/-! # Extending a component eigenvector by zero -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Extend a function on one connected component by zero. -/
def connectedComponentExtendZero
    {V R : Type*} [Zero R] (D : SimpleGraph V)
    (c : D.ConnectedComponent) [DecidablePred (· ∈ c.supp)]
    (t : c.supp → R) : V → R :=
  fun x ↦ if hx : x ∈ c.supp then t ⟨x, hx⟩ else 0

@[simp] theorem connectedComponentExtendZero_apply_mem
    {V R : Type*} [Zero R] (D : SimpleGraph V)
    (c : D.ConnectedComponent) [DecidablePred (· ∈ c.supp)]
    (t : c.supp → R) (x : c.supp) :
    connectedComponentExtendZero D c t x.1 = t x := by
  simp [connectedComponentExtendZero, x.2]

theorem connectedComponentExtendZero_ne_zero
    {V R : Type*} [Zero R] (D : SimpleGraph V)
    (c : D.ConnectedComponent) [DecidablePred (· ∈ c.supp)]
    (t : c.supp → R) (ht : t ≠ 0) :
    connectedComponentExtendZero D c t ≠ 0 := by
  intro hext
  apply ht
  funext x
  have hx := congrFun hext x.1
  simpa using hx

/-- Cast an integral graph eigenvector to a rational eigenvector. -/
theorem adjMatrix_rat_eigenvector_of_int
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (t : V → ℤ) (θ : ℤ)
    (heigen : (D.adjMatrix ℤ).mulVec t = θ • t) :
    (D.adjMatrix ℚ).mulVec (fun x ↦ (t x : ℚ)) =
      (θ : ℚ) • (fun x ↦ (t x : ℚ)) := by
  funext x
  have hx := congrFun heigen x
  rw [Matrix.mulVec, dotProduct] at hx ⊢
  simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
  calc
    (∑ i, D.adjMatrix ℚ x i * (t i : ℚ)) =
        ∑ i, ((D.adjMatrix ℤ x i * t i : ℤ) : ℚ) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [SimpleGraph.adjMatrix_apply]
    _ = ((∑ i, D.adjMatrix ℤ x i * t i : ℤ) : ℚ) := by simp
    _ = ((θ * t x : ℤ) : ℚ) := by rw [hx]
    _ = (θ : ℚ) * (t x : ℚ) := by norm_num

/-- An eigenvector of the graph induced on a connected component extends by
zero to a global eigenvector. -/
theorem adjMatrix_eigenvector_connectedComponentExtendZero
    {V R : Type*} [Fintype V] [DecidableEq V] [Field R]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (c : D.ConnectedComponent) (t : c.supp → R) (θ : R)
    (heigen : ((D.induce c.supp).adjMatrix R).mulVec t = θ • t) :
    (D.adjMatrix R).mulVec (connectedComponentExtendZero D c t) =
      θ • connectedComponentExtendZero D c t := by
  classical
  funext x
  by_cases hx : x ∈ c.supp
  · let xs : c.supp := ⟨x, hx⟩
    rw [adjMatrix_mulVec_eq_induce_mulVec_of_support D c.supp
      (connectedComponentExtendZero D c t)
      (by intro y hy; simp [connectedComponentExtendZero, hy]) xs]
    have hpoint := congrFun heigen xs
    simpa [xs, connectedComponentExtendZero, hx] using hpoint
  · have hno : ∀ y, D.Adj x y → y ∉ c.supp := by
      intro y hxy hy
      have hyc : D.connectedComponentMk y = c :=
        (ConnectedComponent.mem_supp_iff c y).mp hy
      have hxc : D.connectedComponentMk x = c :=
        (ConnectedComponent.connectedComponentMk_eq_of_adj hxy).trans hyc
      exact hx ((ConnectedComponent.mem_supp_iff c x).mpr hxc)
    rw [Matrix.mulVec, dotProduct]
    simp only [Pi.smul_apply, connectedComponentExtendZero, hx, dite_false,
      smul_zero]
    apply Finset.sum_eq_zero
    intro y _hy
    by_cases hxy : D.Adj x y
    · have hy : y ∉ c.supp := hno y hxy
      simp [SimpleGraph.adjMatrix_apply, hxy, hy]
    · simp [SimpleGraph.adjMatrix_apply, hxy]

/-- An integral eigenvector on an induced connected component casts to ℚ and
extends by zero to a global rational eigenvector. -/
theorem adjMatrix_rat_eigenvector_componentExtendZero_of_int
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (c : D.ConnectedComponent) (t : c.supp → ℤ) (θ : ℤ)
    (heigen : ((D.induce c.supp).adjMatrix ℤ).mulVec t = θ • t) :
    (D.adjMatrix ℚ).mulVec
        (connectedComponentExtendZero D c (fun x ↦ (t x : ℚ))) =
      (θ : ℚ) • connectedComponentExtendZero D c (fun x ↦ (t x : ℚ)) := by
  apply adjMatrix_eigenvector_connectedComponentExtendZero
  exact adjMatrix_rat_eigenvector_of_int (D.induce c.supp) t θ heigen

end

end Erdos85

#print axioms Erdos85.adjMatrix_eigenvector_connectedComponentExtendZero
#print axioms Erdos85.connectedComponentExtendZero_ne_zero
#print axioms Erdos85.adjMatrix_rat_eigenvector_componentExtendZero_of_int
