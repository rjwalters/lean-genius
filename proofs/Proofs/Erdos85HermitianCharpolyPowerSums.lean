import Proofs.Erdos85QuadraticFactorRootMoments
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Characteristic-root power sums of a Hermitian matrix

For a Hermitian complex matrix, the `m`-th power sum of the characteristic
roots is the trace of the `m`-th matrix power.  This is the bridge between
polynomial factor arithmetic and closed-walk trace counts.
-/

open Polynomial

namespace Erdos85

noncomputable section

theorem complexRootPowerSum_charpoly_eq_trace_pow
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (m : ℕ) :
    complexRootPowerSum A.charpoly m = Matrix.trace (A ^ m) := by
  let U := hA.eigenvectorUnitary
  let D : Matrix n n ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hs : A = Unitary.conjStarAlgAut ℂ _ U D := by
    simpa [U, D] using hA.spectral_theorem
  have htrace : Matrix.trace (A ^ m) =
      ∑ i, (hA.eigenvalues i : ℂ) ^ m := by
    calc
      Matrix.trace (A ^ m) =
          Matrix.trace ((Unitary.conjStarAlgAut ℂ _ U D) ^ m) :=
        congrArg (fun M : Matrix n n ℂ => Matrix.trace (M ^ m)) hs
      _ = Matrix.trace (Unitary.conjStarAlgAut ℂ _ U (D ^ m)) := by
        rw [map_pow]
      _ = Matrix.trace (D ^ m) := by
        simp only [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
          Unitary.coe_star_mul_self, one_mul]
      _ = ∑ i, (hA.eigenvalues i : ℂ) ^ m := by
        rw [show D ^ m = Matrix.diagonal
          (fun i => (hA.eigenvalues i : ℂ) ^ m) by
            simp [D, Matrix.diagonal_pow]]
        rw [Matrix.trace_diagonal]
  rw [complexRootPowerSum, hA.roots_charpoly_eq_eigenvalues]
  simp only [Multiset.map_map, Function.comp_apply]
  simpa using htrace.symm

/-- The rational adjacency characteristic polynomial, after base change to
`ℂ`, has power sums equal to complex adjacency trace powers. -/
theorem complexRootPowerSum_ratAdjCharpoly_eq_trace_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) :
    complexRootPowerSum
        ((G.adjMatrix ℚ).charpoly.map (algebraMap ℚ ℂ)) m =
      Matrix.trace ((G.adjMatrix ℂ) ^ m) := by
  have hadj : (G.adjMatrix ℚ).map (algebraMap ℚ ℂ) = G.adjMatrix ℂ := by
    ext i j
    simp [SimpleGraph.adjMatrix_apply]
  have hherm : (G.adjMatrix ℂ).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [SimpleGraph.adjMatrix_apply, G.adj_comm]
  rw [← Matrix.charpoly_map, hadj]
  exact complexRootPowerSum_charpoly_eq_trace_pow (G.adjMatrix ℂ) hherm m

/-- Complex adjacency traces are obtained by casting the corresponding
integer adjacency traces. -/
theorem trace_complex_adjMatrix_pow_eq_intCast
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) :
    Matrix.trace ((G.adjMatrix ℂ) ^ m) =
      ((Matrix.trace ((G.adjMatrix ℤ) ^ m) : ℤ) : ℂ) := by
  have hadj : (G.adjMatrix ℤ).map (Int.castRingHom ℂ) = G.adjMatrix ℂ := by
    ext i j
    simp [SimpleGraph.adjMatrix_apply]
  calc
    Matrix.trace ((G.adjMatrix ℂ) ^ m) =
        Matrix.trace (((G.adjMatrix ℤ) ^ m).map (Int.castRingHom ℂ)) := by
      rw [Matrix.map_pow, hadj]
    _ = ((Matrix.trace ((G.adjMatrix ℤ) ^ m) : ℤ) : ℂ) := by
      rw [← AddMonoidHom.map_trace]
      rfl

end

end Erdos85
