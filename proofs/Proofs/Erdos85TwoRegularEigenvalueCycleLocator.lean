import Proofs.Erdos85ComponentFactorization
import Proofs.Erdos85IsCyclesComponentCharpoly

/-! # Locating a two-factor eigenvalue on one cycle component -/

namespace Erdos85

open SimpleGraph Polynomial

noncomputable section

/-- A nonzero adjacency eigenvector of a finite 2-regular graph has its
eigenvalue on one actual cycle component, hence satisfies that component's
rescaled Chebyshev equation. -/
theorem exists_twoRegular_component_chebyshev_root_of_eigenvector
    {V K : Type*} [Fintype V] [DecidableEq V] [Field K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ x, G.degree x = 2)
    (α : K) (v : V → K) (hv0 : v ≠ 0)
    (heigen : (G.adjMatrix K).mulVec v = α • v) :
    ∃ (c : G.ConnectedComponent) (r : ℕ),
      3 ≤ r ∧ r = c.supp.ncard ∧ (Chebyshev.C K (r : ℤ)).eval α = 2 := by
  classical
  let M : Matrix V V K := Matrix.scalar V α - G.adjMatrix K
  have hMv : M.mulVec v = 0 := by
    rw [show M.mulVec v = α • v - (G.adjMatrix K).mulVec v by
      simp [M, Matrix.sub_mulVec]]
    rw [heigen]
    exact sub_self _
  have hdet : M.det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨v, hv0, hMv⟩
  have hfactor := det_resolvent_eq_prod_connectedComponents G α
  change M.det = _ at hfactor
  rw [hfactor] at hdet
  obtain ⟨c, _hc, hcdet⟩ := Finset.prod_eq_zero_iff.mp hdet
  obtain ⟨r, hrthree, hrsize, hpolyZ⟩ :=
    twoRegular_component_charpoly_chebyshev G hdeg c
  have hmapMatrix :
      ((G.induce c.supp).adjMatrix ℤ).map (algebraMap ℤ K) =
        (G.induce c.supp).adjMatrix K := by
    ext a b
    by_cases hab : (G.induce c.supp).Adj a b <;>
      simp [SimpleGraph.adjMatrix_apply]
  have hpolyK :
      ((G.induce c.supp).adjMatrix K).charpoly =
        (Chebyshev.C ℤ (r : ℤ) - 2).map (algebraMap ℤ K) := by
    rw [← hmapMatrix, Matrix.charpoly_map, hpolyZ]
  have hroot :
      ((Chebyshev.C ℤ (r : ℤ) - 2).map (algebraMap ℤ K)).eval α = 0 := by
    rw [← hpolyK, Matrix.eval_charpoly]
    exact hcdet
  have heval : (Chebyshev.C K (r : ℤ)).eval α - 2 = 0 := by
    simpa [eval_sub, eval_map] using hroot
  exact ⟨c, r, hrthree, hrsize, sub_eq_zero.mp heval⟩

end

end Erdos85
