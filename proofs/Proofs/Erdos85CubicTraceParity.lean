import Proofs.Erdos85CubicDiagonalParity
import Proofs.Erdos85SymmetricCubeTraceSquares

/-! # Evenness of the sixth adjacency trace -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- A symmetric integer table whose diagonal entries are even has even total
sum.  The proof removes one row and column at a time; the two off-diagonal
strips agree and therefore contribute twice an integer. -/
theorem even_sum_product_of_symmetric_even_diag
    {X : Type*} (s : Finset X) (f : X → X → ℤ)
    (hsymm : ∀ i ∈ s, ∀ j ∈ s, f i j = f j i)
    (hdiag : ∀ i ∈ s, Even (f i i)) :
    Even (∑ i ∈ s, ∑ j ∈ s, f i j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hsymm_s : ∀ i ∈ s, ∀ j ∈ s, f i j = f j i := by
        intro i hi j hj
        exact hsymm i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj)
      have hdiag_s : ∀ i ∈ s, Even (f i i) := by
        intro i hi
        exact hdiag i (Finset.mem_insert_of_mem hi)
      have hcross : (∑ i ∈ s, f i a) = ∑ i ∈ s, f a i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsymm i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self a s)
      rcases hdiag a (Finset.mem_insert_self a s) with ⟨d, hd⟩
      rcases ih hsymm_s hdiag_s with ⟨r, hr⟩
      refine ⟨d + (∑ i ∈ s, f a i) + r, ?_⟩
      simp_rw [Finset.sum_insert ha]
      rw [Finset.sum_add_distrib]
      rw [hcross, hd, hr]
      ring

/-- The sixth adjacency trace of every finite simple graph is even.  Its
off-diagonal cubic-square terms occur in symmetric pairs, while a diagonal
cubic entry is itself even. -/
theorem even_trace_adjMatrix_pow_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (Matrix.trace ((G.adjMatrix ℤ) ^ 6)) := by
  classical
  let A := G.adjMatrix ℤ
  have hA : A.IsSymm := by
    simpa [A] using (SimpleGraph.isSymm_adjMatrix G ℤ)
  rw [trace_pow_six_eq_sum_cube_apply_sq A hA]
  apply even_sum_product_of_symmetric_even_diag Finset.univ
    (fun i j => (A ^ 3) i j ^ 2)
  · intro i _ j _
    have hcube := hA.pow 3
    have hij : (A ^ 3) i j = (A ^ 3) j i :=
      congrFun (congrFun hcube.eq j) i
    rw [hij]
  · intro i _
    have hi : Even ((A ^ 3) i i) := by
      simpa [A, pow_succ] using even_adjMatrix_cube_apply_self G i
    rcases hi with ⟨k, hk⟩
    refine ⟨2 * k ^ 2, ?_⟩
    rw [hk]
    ring

/-- An even integer strictly above `61248` is at least `61250`. -/
theorem even_strict_sixthMoment_ge_61250 (z : ℤ)
    (heven : Even z) (hstrict : 61248 < z) : 61250 ≤ z := by
  rcases heven with ⟨k, hk⟩
  omega

end

end Erdos85

#print axioms Erdos85.even_sum_product_of_symmetric_even_diag
#print axioms Erdos85.even_trace_adjMatrix_pow_six
#print axioms Erdos85.even_strict_sixthMoment_ge_61250
