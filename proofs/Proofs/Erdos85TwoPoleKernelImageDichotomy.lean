import Proofs.Erdos85AdjacencyKernelResidualTransport
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Two-pole kernel/image dichotomy

This formalizes the linear alternative `(73rnz_ay)--(73rnz_az)`.  For a
symmetric finite matrix, either the two-coordinate indicator is separated
by a kernel vector, or it belongs to the image of the matrix.
-/

open Matrix Module

namespace Erdos85

/-- Finite-dimensional Fredholm alternative specialized to a symmetric
matrix and a two-coordinate right-hand side. -/
theorem exists_kernel_twoCoordinate_separator_or_exists_mulVec_eq_twoCoordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (ZMod 2))
    (hsymm : ∀ i j, M i j = M j i) (E₁ E₂ : ι) :
    (∃ v : ι → ZMod 2, M.mulVec v = 0 ∧ v E₁ + v E₂ = 1) ∨
      ∃ x : ι → ZMod 2,
        M.mulVec x = Pi.single E₁ 1 + Pi.single E₂ 1 := by
  let h : ι → ZMod 2 := Pi.single E₁ 1 + Pi.single E₂ 1
  let L : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) := M.mulVecLin
  by_cases him : h ∈ LinearMap.range L
  · right
    rcases him with ⟨x, hx⟩
    exact ⟨x, by simpa [h, L, Matrix.mulVecLin_apply] using hx⟩
  · left
    have hnall : ¬ ∀ φ : Module.Dual (ZMod 2) (ι → ZMod 2),
        φ ∈ (LinearMap.range L).dualAnnihilator → φ h = 0 := by
      intro hall
      exact him ((Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
        (LinearMap.range L) h).mp hall)
    push Not at hnall
    rcases hnall with ⟨φ, hφ, hφh⟩
    let v : ι → ZMod 2 :=
      (dotProductEquiv (ZMod 2) ι).symm φ
    have hvφ : dotProductEquiv (ZMod 2) ι v = φ := by
      exact LinearEquiv.apply_symm_apply _ φ
    have hφ0 : ∀ y ∈ LinearMap.range L, φ y = 0 := by
      simpa only [Submodule.mem_dualAnnihilator] using hφ
    have hdot (x : ι → ZMod 2) : dotProduct v (M.mulVec x) = 0 := by
      have hrange : M.mulVec x ∈ LinearMap.range L := by
        exact ⟨x, by simp [L]⟩
      calc
        dotProduct v (M.mulVec x) =
            (dotProductEquiv (ZMod 2) ι v) (M.mulVec x) := rfl
        _ = φ (M.mulVec x) := by rw [hvφ]
        _ = 0 := hφ0 _ hrange
    have hMv : M.mulVec v = 0 := by
      funext i
      have hi := hdot (Pi.single i 1)
      have hi' : dotProduct v (M.col i) = 0 := by
        simpa only [Matrix.mulVec_single_one] using hi
      calc
        (M.mulVec v) i = dotProduct (M i) v := rfl
        _ = dotProduct v (M i) := dotProduct_comm _ _
        _ = dotProduct v (M.col i) := by
          congr 1
          funext j
          exact hsymm i j
        _ = 0 := hi'
    have hφh_one : φ h = 1 := by
      exact (show ∀ c : ZMod 2, c ≠ 0 → c = 1 by decide) _ hφh
    have hvsep : v E₁ + v E₂ = 1 := by
      have : dotProduct v h = 1 := by
        calc
          dotProduct v h = (dotProductEquiv (ZMod 2) ι v) h := rfl
          _ = φ h := by rw [hvφ]
          _ = 1 := hφh_one
      simpa only [h, dotProduct_add, dotProduct_single_one] using this
    exact ⟨v, hMv, hvsep⟩

/-- Graph specialization: either two vertices are separated by an ambient
adjacency-kernel character, or their two-pole indicator has an ambient
adjacency potential. -/
theorem exists_adjKernel_twoPole_separator_or_exists_adjPotential
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj] (E₁ E₂ : V) :
    (∃ v : V → ZMod 2,
      (A.adjMatrix (ZMod 2)).mulVec v = 0 ∧ v E₁ + v E₂ = 1) ∨
      ∃ x : V → ZMod 2,
        (A.adjMatrix (ZMod 2)).mulVec x =
          Pi.single E₁ 1 + Pi.single E₂ 1 := by
  apply exists_kernel_twoCoordinate_separator_or_exists_mulVec_eq_twoCoordinate
  intro i j
  exact congr_fun₂ A.isSymm_adjMatrix.eq j i

/-- The dichotomy with the separator horn immediately converted into its
weighted residual/triangle transport equations.  The only alternative left
is the explicit two-pole adjacency potential. -/
theorem exists_starDistinguishing_residualTransport_or_exists_adjPotential
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (E₁ E₂ : V) :
    (∃ v : V → ZMod 2,
      v E₁ + v E₂ = 1 ∧
      ∀ center,
        (∑ z, graphEdgeIndicator (binaryTransportResidualGraph A hq hreg)
          center z * v z) =
        ∑ z, graphEdgeIndicator (triangleFreeEdgeGraph A) center z * v z) ∨
      ∃ x : V → ZMod 2,
        (A.adjMatrix (ZMod 2)).mulVec x =
          Pi.single E₁ 1 + Pi.single E₂ 1 := by
  rcases exists_adjKernel_twoPole_separator_or_exists_adjPotential A E₁ E₂ with
    hsep | hpot
  · left
    exact exists_star_distinguishing_weighted_transport_of_kernel_separator
      A hq hreg E₁ E₂ hsep
  · exact Or.inr hpot

end Erdos85

#print axioms Erdos85.exists_kernel_twoCoordinate_separator_or_exists_mulVec_eq_twoCoordinate
#print axioms Erdos85.exists_adjKernel_twoPole_separator_or_exists_adjPotential
#print axioms Erdos85.exists_starDistinguishing_residualTransport_or_exists_adjPotential
