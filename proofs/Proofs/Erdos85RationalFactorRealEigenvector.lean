import Proofs.Erdos85HermitianFactorRootsReal

/-!
# Real eigenvectors from rational characteristic factors

A complex root of a rational characteristic factor which is known to be real
is realized by a nonzero eigenvector of the real scalar extension of the
ambient rational matrix.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- A real complex root of a rational factor of `A.charpoly` gives a genuine
nonzero real eigenvector of `A` with eigenvalue `z.re`. -/
theorem exists_real_eigenvector_of_mem_roots_map_of_dvd_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ) {p : ℚ[X]}
    (hp : p ≠ 0) (hdiv : p ∣ A.charpoly)
    {z : ℂ} (hz : z ∈ (p.map (algebraMap ℚ ℂ)).roots)
    (hzreal : z.im = 0) :
    ∃ w : n → ℝ, w ≠ 0 ∧
      (A.map (algebraMap ℚ ℝ)).mulVec w = z.re • w := by
  have hpC : p.map (algebraMap ℚ ℂ) ≠ 0 := by
    simpa using (Polynomial.map_injective (algebraMap ℚ ℂ)
      (algebraMap ℚ ℂ).injective).ne hp
  have hzrootC : IsRoot (p.map (algebraMap ℚ ℂ)) z :=
    (mem_roots hpC).mp hz
  have hz_eq : (z.re : ℂ) = z := by
    apply Complex.ext
    · simp
    · simpa using hzreal.symm
  have hzrootRC : IsRoot
      ((p.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ))
      (algebraMap ℝ ℂ z.re) := by
    have hmaps :
        (p.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ) =
          p.map (algebraMap ℚ ℂ) := by
      ext k
      simp
    rw [hmaps]
    simpa [hz_eq] using hzrootC
  have hzrootR : IsRoot (p.map (algebraMap ℚ ℝ)) z.re :=
    (Polynomial.isRoot_map_iff (algebraMap ℝ ℂ).injective).mp hzrootRC
  have hdivR : p.map (algebraMap ℚ ℝ) ∣
      (A.map (algebraMap ℚ ℝ)).charpoly := by
    obtain ⟨r, hr⟩ := hdiv
    refine ⟨r.map (algebraMap ℚ ℝ), ?_⟩
    rw [Matrix.charpoly_map, hr]
    simp
  obtain ⟨r, hr⟩ := hdivR
  have hzchar : IsRoot (A.map (algebraMap ℚ ℝ)).charpoly z.re := by
    rw [hr, IsRoot, eval_mul, hzrootR.eq_zero, zero_mul]
  let AR := A.map (algebraMap ℚ ℝ)
  have hzlin : IsRoot AR.toLin'.charpoly z.re := by
    simpa [AR, Matrix.charpoly_toLin'] using hzchar
  have heig : Module.End.HasEigenvalue AR.toLin' z.re :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly AR.toLin' z.re).mpr hzlin
  obtain ⟨w, hw⟩ := heig.exists_hasEigenvector
  refine ⟨w, hw.2, ?_⟩
  simpa [AR, Matrix.toLin'_apply] using hw.apply_eq_smul

/-- Hermitian wrapper: reality of the mapped root and existence of its real
eigenvector are both discharged from rational characteristic divisibility. -/
theorem exists_real_eigenvector_of_mem_roots_map_of_dvd_hermitian_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ)
    (hA : (A.map (algebraMap ℚ ℂ)).IsHermitian)
    {p : ℚ[X]} (hp : p ≠ 0) (hdiv : p ∣ A.charpoly)
    {z : ℂ} (hz : z ∈ (p.map (algebraMap ℚ ℂ)).roots) :
    z.im = 0 ∧
      ∃ w : n → ℝ, w ≠ 0 ∧
        (A.map (algebraMap ℚ ℝ)).mulVec w = z.re • w := by
  have hzreal := im_eq_zero_of_mem_roots_map_of_dvd_rat_charpoly
    A hA hp hdiv hz
  exact ⟨hzreal,
    exists_real_eigenvector_of_mem_roots_map_of_dvd_charpoly
      A hp hdiv hz hzreal⟩

#print axioms exists_real_eigenvector_of_mem_roots_map_of_dvd_charpoly
#print axioms
  exists_real_eigenvector_of_mem_roots_map_of_dvd_hermitian_charpoly

end

end Erdos85
