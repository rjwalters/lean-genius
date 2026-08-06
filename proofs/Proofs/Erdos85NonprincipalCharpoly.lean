import Proofs.Erdos85OrbitFactorExtraction
import Proofs.Erdos85AdjoinSquareConjugation
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# The nonprincipal adjacency characteristic factor

For a finite regular simple graph, the constant vector supplies the principal
adjacency root `d`.  Removing `X-d` from the rational characteristic
polynomial leaves a monic positive-degree factor whose subleading coefficient
records the nonzero nonprincipal trace.  The orbit extraction theorem then
produces an asymmetric irreducible adjacency orbit.
-/

namespace Erdos85

open Polynomial
open scoped Polynomial

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem scalar_mulVec_one_rat (a : ℚ) (i : V) :
    (Matrix.scalar V a).mulVec (Function.const V (1 : ℚ)) i = a := by
  have h1 : (Matrix.scalar V a).mulVec (Function.const V (1 : ℚ)) i =
      ∑ j : V, Matrix.scalar V a i j * 1 := rfl
  rw [h1]
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply, mul_one]
  rw [Finset.sum_eq_single i
    (fun j _ hji => by simp [Ne.symm hji])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

theorem adjMatrix_charpoly_eval_degree_rat
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (d : ℕ) (hreg : ∀ v : V, G.degree v = d) :
    (G.adjMatrix ℚ).charpoly.eval (d : ℚ) = 0 := by
  rw [Matrix.eval_charpoly]
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (i := Classical.arbitrary V)
  · ext i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hreg i,
      scalar_mulVec_one_rat]
  · simp

theorem X_sub_degree_dvd_adjMatrix_charpoly_rat
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (d : ℕ) (hreg : ∀ v : V, G.degree v = d) :
    (Polynomial.X - Polynomial.C (d : ℚ)) ∣ (G.adjMatrix ℚ).charpoly := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact adjMatrix_charpoly_eval_degree_rat G d hreg

omit [DecidableEq V] in
theorem adjMatrix_trace_rat_eq_zero (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix.trace (G.adjMatrix ℚ) = 0 := by
  simp [Matrix.trace, Matrix.diag, SimpleGraph.adjMatrix_apply]

/-- A graph-facing package for the complementary characteristic factor. -/
theorem exists_nonprincipalCharpoly_factor
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (d : ℕ) (hcard : 2 ≤ Fintype.card V)
    (hreg : ∀ v : V, G.degree v = d) :
    ∃ q : Polynomial ℚ,
      (G.adjMatrix ℚ).charpoly =
        (Polynomial.X - Polynomial.C (d : ℚ)) * q ∧
      q.Monic ∧ 0 < q.natDegree ∧
      ((Polynomial.X - Polynomial.C (d : ℚ)) * q).coeff q.natDegree = 0 := by
  obtain ⟨q, hq⟩ := X_sub_degree_dvd_adjMatrix_charpoly_rat G d hreg
  have hlin : (Polynomial.X - Polynomial.C (d : ℚ)).Monic :=
    Polynomial.monic_X_sub_C _
  have hqmonic : q.Monic := hlin.of_mul_monic_left (hq ▸ Matrix.charpoly_monic _)
  have hq0 : q ≠ 0 := hqmonic.ne_zero
  have hqdeg : q.natDegree = Fintype.card V - 1 := by
    have hdeg := Polynomial.natDegree_mul hlin.ne_zero hq0
    rw [← hq, Matrix.charpoly_natDegree_eq_dim] at hdeg
    have hlinDeg : (Polynomial.X - Polynomial.C (d : ℚ)).natDegree = 1 :=
      Polynomial.natDegree_X_sub_C _
    rw [hlinDeg] at hdeg
    omega
  have hqpos : 0 < q.natDegree := by omega
  refine ⟨q, hq, hqmonic, hqpos, ?_⟩
  have htrace := Matrix.trace_eq_neg_charpoly_coeff (G.adjMatrix ℚ)
  rw [adjMatrix_trace_rat_eq_zero G] at htrace
  have hcoeff : (G.adjMatrix ℚ).charpoly.coeff (Fintype.card V - 1) = 0 := by
    linarith
  rw [hq, ← hqdeg] at hcoeff
  exact hcoeff

/-- Every nontrivial positive-degree regular graph has an asymmetric
irreducible factor in its nonprincipal adjacency characteristic polynomial. -/
theorem exists_asymmetric_nonprincipal_irreducible
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (d : ℕ) (hd : 0 < d) (hcard : 2 ≤ Fintype.card V)
    (hreg : ∀ v : V, G.degree v = d) :
    ∃ q f : Polynomial ℚ,
      (G.adjMatrix ℚ).charpoly =
        (Polynomial.X - Polynomial.C (d : ℚ)) * q ∧
      Irreducible f ∧ f.Monic ∧ f ∣ q ∧ Polynomial.signedReflection f ≠ f := by
  obtain ⟨q, hfactor, hqmonic, hqdeg, htrace⟩ :=
    exists_nonprincipalCharpoly_factor G d hcard hreg
  obtain ⟨f, hfirr, hfmonic, hfdvd, hfasym⟩ :=
    Polynomial.exists_irreducible_dvd_not_reflection_fixed_of_linearFactor_trace_zero
      q hqmonic hqdeg (d : ℚ) (by exact_mod_cast hd.ne') htrace
  exact ⟨q, f, hfactor, hfirr, hfmonic, hfdvd, hfasym⟩

/-- The asymmetric factor has a root in the algebraic closure, and that root
also annihilates the nonprincipal characteristic factor. -/
theorem exists_asymmetric_nonprincipal_root
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (d : ℕ) (hd : 0 < d) (hcard : 2 ≤ Fintype.card V)
    (hreg : ∀ v : V, G.degree v = d) :
    ∃ (q f : Polynomial ℚ) (θ : AlgebraicClosure ℚ),
      (G.adjMatrix ℚ).charpoly =
        (Polynomial.X - Polynomial.C (d : ℚ)) * q ∧
      Irreducible f ∧ f.Monic ∧ f ∣ q ∧
      Polynomial.signedReflection f ≠ f ∧
      Polynomial.aeval θ f = 0 ∧ Polynomial.aeval θ q = 0 ∧
      Polynomial.aeval θ (G.adjMatrix ℚ).charpoly = 0 ∧
      θ ∈ IntermediateField.adjoin ℚ {θ ^ 2} := by
  obtain ⟨q, f, hfactor, hfirr, hfmonic, hfdvd, hfasym⟩ :=
    exists_asymmetric_nonprincipal_irreducible G d hd hcard hreg
  let ι : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ)
  have hdeg : (f.map ι).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective ι.injective]
    exact (Polynomial.degree_pos_of_irreducible hfirr).ne'
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_root (f.map ι) hdeg
  have hθf : Polynomial.aeval θ f = 0 := by
    simpa [Polynomial.aeval_def, ι] using hθ.eq_zero
  have hθq : Polynomial.aeval θ q = 0 := by
    obtain ⟨r, hr⟩ := hfdvd
    rw [hr, map_mul, hθf, zero_mul]
  have hθchar : Polynomial.aeval θ (G.adjMatrix ℚ).charpoly = 0 := by
    rw [hfactor, map_mul, hθq, mul_zero]
  have hθmem : θ ∈ IntermediateField.adjoin ℚ {θ ^ 2} :=
    mem_adjoin_sq_of_aeval_eq_zero_of_signedReflection_ne
      f hfirr hfmonic hfasym θ hθf
  exact ⟨q, f, θ, hfactor, hfirr, hfmonic, hfdvd, hfasym, hθf, hθq,
    hθchar, hθmem⟩

/-- A rational characteristic root in the algebraic closure is represented by
a genuine adjacency eigenvector after scalar extension. -/
theorem exists_adjMatrix_eigenvector_of_aeval_charpoly_eq_zero
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (θ : AlgebraicClosure ℚ)
    (hθ : Polynomial.aeval θ (G.adjMatrix ℚ).charpoly = 0) :
    ∃ v : V → AlgebraicClosure ℚ,
      v ≠ 0 ∧ (G.adjMatrix (AlgebraicClosure ℚ)).mulVec v = θ • v := by
  let ι : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ)
  have hAmap : (G.adjMatrix ℚ).map ι = G.adjMatrix (AlgebraicClosure ℚ) := by
    ext i j
    simp [SimpleGraph.adjMatrix_apply, ι]
  have hroot : Polynomial.IsRoot
      (G.adjMatrix (AlgebraicClosure ℚ)).charpoly θ := by
    change (G.adjMatrix (AlgebraicClosure ℚ)).charpoly.eval θ = 0
    rw [← hAmap, Matrix.charpoly_map]
    simpa [Polynomial.aeval_def, ι] using hθ
  have hspec : θ ∈ spectrum (AlgebraicClosure ℚ)
      (G.adjMatrix (AlgebraicClosure ℚ)) :=
    Matrix.mem_spectrum_of_isRoot_charpoly hroot
  have heig : Module.End.HasEigenvalue
      (G.adjMatrix (AlgebraicClosure ℚ)).toLin' θ :=
    Module.End.HasEigenvalue.of_mem_spectrum (by simpa using hspec)
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  exact ⟨v, hv.2, hv.apply_eq_smul⟩

end Erdos85
