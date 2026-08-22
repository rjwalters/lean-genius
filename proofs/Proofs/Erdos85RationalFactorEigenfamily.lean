import Proofs.Erdos85RationalFactorRealEigenvector

/-!
# Multiplicity-indexed real eigenfamilies from rational factors

The root multiset of a rational characteristic factor is converted to a
`Fin`-indexed family.  Repeated roots occupy distinct indices, so algebraic
multiplicity is preserved exactly.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- A rational characteristic factor of a Hermitian matrix supplies a real
eigenvector for every complex root occurrence, and the sum of the resulting
real eigenvalues is the real part of the root-multiset sum. -/
theorem exists_real_eigenfamily_of_rat_charpoly_factor
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℚ)
    (hA : (A.map (algebraMap ℚ ℂ)).IsHermitian)
    {p : ℚ[X]} (hp : p ≠ 0) (hdiv : p ∣ A.charpoly) :
    let roots := (p.map (algebraMap ℚ ℂ)).roots
    let L := roots.toList
    ∃ (θ : Fin L.length → ℝ) (w : Fin L.length → n → ℝ),
      (∀ i, w i ≠ 0) ∧
      (∀ i, (A.map (algebraMap ℚ ℝ)).mulVec (w i) = θ i • w i) ∧
      ∑ i, θ i = roots.sum.re := by
  dsimp only
  let roots := (p.map (algebraMap ℚ ℂ)).roots
  let L := roots.toList
  have hroot : ∀ i : Fin L.length, L[i] ∈ roots := by
    intro i
    rw [← Multiset.mem_toList]
    change L[i] ∈ L
    exact L.get_mem i
  have hex : ∀ i : Fin L.length,
      ∃ w : n → ℝ, w ≠ 0 ∧
        (A.map (algebraMap ℚ ℝ)).mulVec w = L[i].re • w := by
    intro i
    exact (exists_real_eigenvector_of_mem_roots_map_of_dvd_hermitian_charpoly
      A hA hp hdiv (hroot i)).2
  choose w hw heigen using hex
  refine ⟨fun i ↦ L[i].re, w, hw, heigen, ?_⟩
  have hreList : (L.map Complex.re).sum = L.sum.re := by
    induction L with
    | nil => simp
    | cons z L ih => simp [ih]
  calc
    ∑ i : Fin L.length, L[i].re = (L.map Complex.re).sum := by
      simpa using (Fin.sum_univ_fun_getElem (L.map Complex.re)).symm
    _ = L.sum.re := hreList
    _ = roots.sum.re := by
      rw [← Multiset.sum_toList]

#print axioms exists_real_eigenfamily_of_rat_charpoly_factor

end

end Erdos85
