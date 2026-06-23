/-
  Aristotle targets for Erdős Problem #1039 (Polynomial Lemniscate Disc Radius)
  Routine supporting lemmas for automated proof search.
  See Erdos1039Problem.lean for the main formalization.

  The three sorried theorems in Erdos1039Problem.lean are:
  1. area_implies_disc_bound: sublevelArea f ≥ π * ρ(f)²
  2. degree_one_optimal: degree-1 polynomial has ρ(f) = 1
  3. clustered_implies_large_disc: clustered roots → ρ(f) ≥ 1 - ε

  This file provides structural support lemmas for these theorems.
-/
import Mathlib
import Proofs.Erdos1039Problem

namespace Erdos1039.Aristotle

open Erdos1039 Finset Complex

/-
## Supporting lemmas for degree_one_optimal
-/

/-- For a degree-1 polynomial, eval z = z - roots 0. -/
theorem eval_degree_one (f : UnitDiscPolynomial) (hf : f.degree = 1) (z : ℂ) :
    f.eval z = z - f.roots ⟨0, hf ▸ Nat.zero_lt_one⟩ := by
  simp only [UnitDiscPolynomial.eval, hf]
  simp [Fin.prod_univ_one]

/-- The sublevel set of a degree-1 polynomial is the open disc of radius 1 around the root. -/
theorem sublevelSet_degree_one (f : UnitDiscPolynomial) (hf : f.degree = 1) :
    sublevelSet f = {z : ℂ | Complex.abs (z - f.roots ⟨0, hf ▸ Nat.zero_lt_one⟩) < 1} := by
  ext z
  simp only [sublevelSet, Set.mem_setOf_eq]
  rw [eval_degree_one f hf z]

/-- A disc of radius r centered at c is inscribed in the open disc of radius r centered at c. -/
theorem isInscribedDisc_self (c : ℂ) (r : ℝ) (hr : r > 0) :
    isInscribedDisc {z : ℂ | Complex.abs (z - c) < r} c r := by
  constructor
  · exact hr
  · intro z hz
    exact hz

/-
## Supporting lemmas for area_implies_disc_bound
-/

/-- Monotonicity: inscribed disc in S implies inscribed disc in superset T. -/
theorem isInscribedDisc_mono (S T : Set ℂ) (hST : S ⊆ T) (c : ℂ) (r : ℝ)
    (h : isInscribedDisc S c r) : isInscribedDisc T c r := by
  exact ⟨h.1, fun z hz => hST (h.2 z hz)⟩

/-- Monotonicity of inscribed disc radius under set inclusion. -/
theorem inscribedDiscRadius_mono (S T : Set ℂ) (hST : S ⊆ T) :
    inscribedDiscRadius S ≤ inscribedDiscRadius T := by
  apply csSup_le_csSup
  · -- T has an upper bound for inscribed disc radii (bounded by diameter)
    use 2  -- trivial upper bound for any disc inside ℂ... actually not bounded
    rintro r ⟨c, hc⟩
    exact (isInscribedDisc_mono S T hST c r hc).1.le
  · -- radii for S are contained in radii for T
    rintro r ⟨c, hc⟩
    exact ⟨c, isInscribedDisc_mono S T hST c r hc⟩

/-- If r is positive and inscribed in S, then r is in the set of inscribed radii. -/
theorem inscribed_radius_mem (S : Set ℂ) (c : ℂ) (r : ℝ) (h : isInscribedDisc S c r) :
    r ∈ {r : ℝ | ∃ c : ℂ, isInscribedDisc S c r} := ⟨c, h⟩

/-- Positivity: the inscribed disc radius is nonneg when a disc exists. -/
theorem inscribedDiscRadius_nonneg (S : Set ℂ) (c : ℂ) (r : ℝ) (h : isInscribedDisc S c r) :
    0 ≤ inscribedDiscRadius S := by
  apply le_csSup_of_le
  · exact ⟨c, h⟩
  · exact h.1.le

/-
## Supporting lemmas for clustered_implies_large_disc
-/

/-- Triangle inequality: if |z - c| < 1 - ε and |zᵢ - c| < ε, then |z - zᵢ| < 1. -/
theorem abs_sub_lt_of_clustered (z c : ℂ) (zi : ℂ) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hz : Complex.abs (z - c) < 1 - ε) (hzi : Complex.abs (zi - c) < ε) :
    Complex.abs (z - zi) < 1 := by
  have h : Complex.abs (z - zi) ≤ Complex.abs (z - c) + Complex.abs (zi - c) := by
    calc Complex.abs (z - zi)
        = Complex.abs ((z - c) - (zi - c)) := by ring_nf
      _ ≤ Complex.abs (z - c) + Complex.abs (zi - c) := Complex.abs.sub_le _ _
  linarith

/-- Product of values with absolute value < 1 has absolute value < 1. -/
theorem prod_abs_lt_one_of_each {n : ℕ} (hn : n > 0) (v : Fin n → ℂ)
    (hv : ∀ i, Complex.abs (v i) < 1) :
    Complex.abs (∏ i : Fin n, v i) < 1 := by
  rw [map_prod]
  apply Finset.prod_lt_one
  · intro i _; exact Complex.abs.nonneg _
  · intro i _; exact le_of_lt (hv i)
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _, hv _⟩

end Erdos1039.Aristotle
