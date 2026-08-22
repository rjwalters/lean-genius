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

#print axioms im_eq_zero_of_mem_roots_of_dvd_hermitian_charpoly

end

end Erdos85
