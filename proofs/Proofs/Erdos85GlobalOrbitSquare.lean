import Proofs.Erdos85RootMultiplicityStrip
import Proofs.Erdos85AdjacencyDefectEigenvector

open Polynomial

/-!
# The global adjacency-orbit square constraint

A positive-degree regular simple graph has zero adjacency trace and the
regular eigenvalue `d`.  After stripping its full multiplicity, an asymmetric
irreducible adjacency orbit remains and avoids `d`.  A root `θ` of that orbit
is therefore genuinely nonprincipal.  The second-order defect identity sends
its eigenvector to defect eigenvalue `μ = d - 1 - θ²`, while asymmetry puts
`θ` in `ℚ(θ²) = ℚ(μ)`.  Thus `d - 1 - μ` is a square already in `ℚ(μ)`.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- A nonzero root and zero subleading coefficient prevent a nonzero root
from occupying the entire degree of a monic rational polynomial. -/
theorem Polynomial.rootMultiplicity_lt_natDegree_of_monic_of_nextCoeff_eq_zero
    (g : Polynomial ℚ) (hg : g.Monic) (d : ℚ) (hd : d ≠ 0)
    (hroot : g.eval d = 0) (htrace : g.nextCoeff = 0) :
    rootMultiplicity d g < g.natDegree := by
  have hdegpos : 0 < g.natDegree := by
    by_contra h
    have hdeg0 : g.natDegree = 0 := Nat.eq_zero_of_not_pos h
    have hg1 : g = 1 := hg.natDegree_eq_zero.mp hdeg0
    simp [hg1] at hroot
  by_contra hlt
  have hle : g.natDegree ≤ rootMultiplicity d g := Nat.le_of_not_gt hlt
  have hdvd : (X - C d) ^ g.natDegree ∣ g :=
    (le_rootMultiplicity_iff hg.ne_zero).mp hle
  have hpowmonic : ((X - C d) ^ g.natDegree).Monic :=
    (monic_X_sub_C d).pow _
  have hpowdeg : ((X - C d) ^ g.natDegree).natDegree = g.natDegree := by
    rw [(monic_X_sub_C d).natDegree_pow, natDegree_X_sub_C, mul_one]
  have heq : g = (X - C d) ^ g.natDegree :=
    eq_of_monic_of_dvd_of_natDegree_le hpowmonic hg hdvd (by rw [hpowdeg])
  have hn : (g.natDegree : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hdegpos.ne'
  have hnext : g.nextCoeff = -(g.natDegree : ℚ) * d := by
    calc
      g.nextCoeff = ((X - C d) ^ g.natDegree).nextCoeff :=
        congrArg Polynomial.nextCoeff heq
      _ = -(g.natDegree : ℚ) * d := by
        rw [(monic_X_sub_C d).nextCoeff_pow, nextCoeff_X_sub_C,
          nsmul_eq_mul, mul_neg]
        ring
  rw [htrace] at hnext
  have hz : (g.natDegree : ℚ) * d = 0 := by linarith [hnext]
  exact (mul_ne_zero hn hd) hz

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The rational adjacency characteristic polynomial has an asymmetric
irreducible factor which avoids the regular eigenvalue, even when that
eigenvalue has multiplicity greater than one. -/
theorem exists_asymmetric_adjCharpoly_factor_avoiding_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ x, G.degree x = d) :
    ∃ f : Polynomial ℚ, Irreducible f ∧ f.Monic ∧
      f ∣ (G.adjMatrix ℚ).charpoly ∧
      Polynomial.signedReflection f ≠ f ∧ f.eval (d : ℚ) ≠ 0 := by
  let g := (G.adjMatrix ℚ).charpoly
  have hg : g.Monic := Matrix.charpoly_monic _
  have hroot : g.eval (d : ℚ) = 0 :=
    adjMatrix_charpoly_eval_degree_rat G d hreg
  have htrace : g.nextCoeff = 0 := by
    have ht := Matrix.trace_eq_neg_charpoly_nextCoeff (G.adjMatrix ℚ)
    rw [adjMatrix_trace_rat_eq_zero G] at ht
    linarith
  have hdeg := Polynomial.rootMultiplicity_lt_natDegree_of_monic_of_nextCoeff_eq_zero
    g hg (d : ℚ) (by exact_mod_cast hd.ne') hroot htrace
  exact Polynomial.exists_asymmetric_factor_avoiding_root
    g hg (d : ℚ) (by exact_mod_cast hd.ne') hroot htrace hdeg

/-- **Global orbit-square constraint.**  Every positive-degree regular
`C₄`-free graph has a genuine nonprincipal adjacency eigenvector whose
corresponding second-order defect eigenvalue `μ` satisfies that
`d - 1 - μ` has a square root in the field `ℚ(μ)` itself. -/
theorem exists_nonprincipal_defectEigenvalue_with_square
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Nonempty V] (hfree : ¬ containsC4 V G)
    (d : ℕ) (hd : 0 < d) (hreg : ∀ x, G.degree x = d) :
    ∃ (f : Polynomial ℚ) (θ μ : AlgebraicClosure ℚ)
        (v : V → AlgebraicClosure ℚ) (t : AlgebraicClosure ℚ),
      Irreducible f ∧ f.Monic ∧
      f ∣ (G.adjMatrix ℚ).charpoly ∧
      Polynomial.signedReflection f ≠ f ∧
      Polynomial.aeval θ f = 0 ∧ θ ≠ (d : AlgebraicClosure ℚ) ∧
      v ≠ 0 ∧
      (G.adjMatrix (AlgebraicClosure ℚ)).mulVec v = θ • v ∧
      μ = (d : AlgebraicClosure ℚ) - 1 - θ ^ 2 ∧
      ((secondOrderDefectGraph G).adjMatrix (AlgebraicClosure ℚ)).mulVec v = μ • v ∧
      t ∈ IntermediateField.adjoin ℚ {μ} ∧
      t * t = (((d : ℚ) - 1 : ℚ) : AlgebraicClosure ℚ) - μ := by
  obtain ⟨f, hfirr, hfmonic, hfdvd, hfasym, hfavoid⟩ :=
    exists_asymmetric_adjCharpoly_factor_avoiding_degree G d hd hreg
  let ι : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ)
  have hdeg : (f.map ι).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective ι.injective]
    exact (Polynomial.degree_pos_of_irreducible hfirr).ne'
  obtain ⟨θ, hθroot'⟩ := IsAlgClosed.exists_root (f.map ι) hdeg
  have hθroot : Polynomial.aeval θ f = 0 := by
    simpa [Polynomial.aeval_def, ι] using hθroot'.eq_zero
  have hθchar : Polynomial.aeval θ (G.adjMatrix ℚ).charpoly = 0 := by
    obtain ⟨q, hq⟩ := hfdvd
    rw [hq, map_mul, hθroot, zero_mul]
  have hθne : θ ≠ (d : AlgebraicClosure ℚ) := by
    intro hθd
    subst θ
    have hz : algebraMap ℚ (AlgebraicClosure ℚ) (f.eval (d : ℚ)) = 0 := by
      simpa [Polynomial.aeval_def] using hθroot
    have hzQ : f.eval (d : ℚ) = 0 :=
      (algebraMap ℚ (AlgebraicClosure ℚ)).injective (by simpa using hz)
    exact hfavoid hzQ
  obtain ⟨v, hv0, hvA⟩ :=
    exists_adjMatrix_eigenvector_of_aeval_charpoly_eq_zero G _ hθchar
  let μ : AlgebraicClosure ℚ := (d : AlgebraicClosure ℚ) - 1 - θ ^ 2
  have hvD : ((secondOrderDefectGraph G).adjMatrix
      (AlgebraicClosure ℚ)).mulVec v = μ • v :=
    secondOrderDefect_mulVec_of_adj_eigenvector_ne_degree
      G hfree hreg hθne v hvA
  have hμ : μ = (((d : ℚ) - 1 : ℚ) : AlgebraicClosure ℚ) - θ ^ 2 := by
    dsimp [μ]
    push_cast
    ring
  obtain ⟨t, htmem, htsq⟩ := exists_sq_root_of_asymmetric_factor
    ((d : ℚ) - 1) f hfirr hfmonic hfasym θ hθroot μ hμ
  exact ⟨f, θ, μ, v, t, hfirr, hfmonic, hfdvd, hfasym, hθroot,
    hθne, hv0, hvA, rfl, hvD, htmem, htsq⟩

end

end Erdos85
