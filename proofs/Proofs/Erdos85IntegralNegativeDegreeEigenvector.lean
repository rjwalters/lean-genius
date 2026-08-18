import Proofs.Erdos85NegativeDegreeEigenvectorRigidity

/-!
# Integral realization of a complex negative adjacency mode

For an integral adjacency matrix, singularity of `A + kI` does not depend on
whether it is detected over `ℂ` or over `ℤ`.  This bridge converts a complex
`-k` eigenmode into a nonzero integral one, allowing the campaign's existing
integer negative-degree rigidity lemmas to consume spectral transport output.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- A nonzero complex `-k` adjacency eigenvector of a finite graph has a
nonzero integral realization at the same eigenvalue. -/
theorem exists_int_negativeAdjacencyEigenvector_of_complex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℤ) (v : V → ℂ) (hv : v ≠ 0)
    (heig : (G.adjMatrix ℂ).mulVec v = (-k : ℂ) • v) :
    ∃ w : V → ℤ, w ≠ 0 ∧
      (G.adjMatrix ℤ).mulVec w = (-k) • w := by
  let AZ := G.adjMatrix ℤ
  let AC := G.adjMatrix ℂ
  let MZ := AZ + k • (1 : Matrix V V ℤ)
  let MC := AC + (k : ℂ) • (1 : Matrix V V ℂ)
  have hMCv : MC.mulVec v = 0 := by
    simp only [MC, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, AC, heig]
    module
  have hdetC : MC.det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hMCv⟩
  have hmap : MZ.map (Int.castRingHom ℂ) = MC := by
    ext i j
    simp only [MZ, MC, AZ, AC, Matrix.map_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply]
    by_cases hij : i = j <;>
      by_cases hadj : G.Adj i j <;>
        simp [SimpleGraph.adjMatrix_apply, hij, hadj]
  have hcastdet : ((MZ.det : ℤ) : ℂ) = 0 := by
    change (Int.castRingHom ℂ) MZ.det = 0
    rw [(Int.castRingHom ℂ).map_det MZ]
    have hmap' : (Int.castRingHom ℂ).mapMatrix MZ = MC := by
      ext i j
      exact congrFun (congrFun hmap i) j
    rw [hmap', hdetC]
  have hdetZ : MZ.det = 0 := by
    exact_mod_cast hcastdet
  obtain ⟨w, hw, hMZw⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdetZ
  refine ⟨w, hw, ?_⟩
  simp only [MZ, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec] at hMZw
  have hneg := eq_neg_of_add_eq_zero_left hMZw
  simpa only [AZ, neg_smul] using hneg

end


end Erdos85

#print axioms Erdos85.exists_int_negativeAdjacencyEigenvector_of_complex
