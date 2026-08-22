import Mathlib.Analysis.Matrix.Spectrum

/-!
# Roots of Hermitian characteristic factors are real

Any polynomial factor of a Hermitian complex matrix's characteristic
polynomial inherits the reality of its roots.  This small bridge lets a
rational primary restriction be handled through its characteristic factor,
without identifying its scalar-extended kernel explicitly.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- Every root of a nonzero characteristic-polynomial factor of a Hermitian
matrix has zero imaginary part. -/
theorem im_eq_zero_of_mem_roots_of_dvd_hermitian_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    {p : ℂ[X]} (hp : p ≠ 0) (hdiv : p ∣ A.charpoly)
    {z : ℂ} (hz : z ∈ p.roots) : z.im = 0 := by
  have hzroot : IsRoot p z := (mem_roots hp).mp hz
  obtain ⟨r, hr⟩ := hdiv
  have hzcharRoot : IsRoot A.charpoly z := by
    rw [hr]
    rw [IsRoot, eval_mul, hzroot.eq_zero, zero_mul]
  have hzchar : z ∈ A.charpoly.roots :=
    (mem_roots (Matrix.charpoly_monic A).ne_zero).2 hzcharRoot
  rw [hA.roots_charpoly_eq_eigenvalues] at hzchar
  simp only [Multiset.mem_map] at hzchar
  obtain ⟨x, _, hx⟩ := hzchar
  rw [← hx]
  simp

/-- Rational-matrix form: after embedding into `ℂ`, every root of a
rational characteristic factor of a Hermitian matrix is real. -/
theorem im_eq_zero_of_mem_roots_map_of_dvd_rat_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ)
    (hA : (A.map (algebraMap ℚ ℂ)).IsHermitian)
    {p : ℚ[X]} (hp : p ≠ 0) (hdiv : p ∣ A.charpoly)
    {z : ℂ} (hz : z ∈ (p.map (algebraMap ℚ ℂ)).roots) :
    z.im = 0 := by
  have hpmap : p.map (algebraMap ℚ ℂ) ≠ 0 :=
    by simpa using (Polynomial.map_injective (algebraMap ℚ ℂ)
      (algebraMap ℚ ℂ).injective).ne hp
  have hdivmap : p.map (algebraMap ℚ ℂ) ∣
      (A.map (algebraMap ℚ ℂ)).charpoly := by
    obtain ⟨r, hr⟩ := hdiv
    refine ⟨r.map (algebraMap ℚ ℂ), ?_⟩
    rw [Matrix.charpoly_map, hr]
    simp
  exact im_eq_zero_of_mem_roots_of_dvd_hermitian_charpoly
    (A.map (algebraMap ℚ ℂ)) hA hpmap hdivmap hz

#print axioms im_eq_zero_of_mem_roots_of_dvd_hermitian_charpoly
#print axioms im_eq_zero_of_mem_roots_map_of_dvd_rat_charpoly

end

end Erdos85
