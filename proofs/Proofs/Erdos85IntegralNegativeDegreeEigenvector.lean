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

/-- The usual spectral bipartiteness criterion, connected to the campaign's
complex adjacency convention: a connected regular graph carrying a nonzero
mode at the negative degree is bipartite. -/
theorem isBipartite_of_connected_regular_complex_negativeDegree_eigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (k : ℕ) (hreg : ∀ x, G.degree x = k)
    (v : V → ℂ) (hv : v ≠ 0)
    (heig : (G.adjMatrix ℂ).mulVec v = (-(k : ℤ) : ℂ) • v) :
    G.IsBipartite := by
  obtain ⟨w, hw, hwEig⟩ :=
    exists_int_negativeAdjacencyEigenvector_of_complex G (k : ℤ) v hv heig
  have hwSum : ∀ x,
      ∑ y ∈ G.neighborFinset x, w y = -(k : ℤ) * w x := by
    intro x
    have hx := congrFun hwEig x
    rw [SimpleGraph.adjMatrix_mulVec_apply] at hx
    simpa [Pi.smul_apply, smul_eq_mul] using hx
  obtain ⟨a, ha0, habs, hflip⟩ :=
    negativeDegree_harmonic_constant_abs_and_edge_neg
      G hconn k hreg w hwSum
  have hapos : 0 < a := by
    have hane : a ≠ 0 := by
      intro ha
      apply hw
      funext x
      exact abs_eq_zero.mp (by rw [habs x, ha])
    omega
  let P : Set V := {x | 0 < w x}
  let N : Set V := {x | w x < 0}
  apply SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mpr
  refine ⟨P, N, ?_⟩
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    intro x hxP hxN
    change 0 < w x at hxP
    change w x < 0 at hxN
    omega
  · intro x y hxy
    have hxne : w x ≠ 0 := by
      intro hx
      have := habs x
      rw [hx, abs_zero] at this
      omega
    have hyflip := hflip x y hxy
    by_cases hxpos : 0 < w x
    · left
      constructor
      · exact hxpos
      · change w y < 0
        rw [hyflip]
        omega
    · right
      have hxneg : w x < 0 := by omega
      constructor
      · exact hxneg
      · change 0 < w y
        rw [hyflip]
        omega

end


end Erdos85

#print axioms Erdos85.exists_int_negativeAdjacencyEigenvector_of_complex
#print axioms Erdos85.isBipartite_of_connected_regular_complex_negativeDegree_eigenvector
