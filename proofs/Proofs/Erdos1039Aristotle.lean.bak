/-
  Aristotle targets for Erdős Problem #1039: Polynomial Lemniscate Disc Radius
  Routine supporting lemmas for automated proof search.
  See Erdos1039Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (ehpConjecture — open)
  - NOT deep results (Pommerenke, KLR bounds — require complex analysis)
  - Routine properties: inscribed disc definitions, sublevel set membership
  - Logical implications and monotonicity facts
  - No axioms, no definition sorries, no open conjectures
  - No /-! docstring sections (use /- instead)

  Included targets:
  - isInscribedDisc_pos_ari: inscribed disc radius is positive (from definition)
  - isInscribedDisc_mono_ari: smaller radius ⇒ still inscribed
  - inscribedDiscRadius_nonneg_ari: rho is non-negative
  - degree_one_sublevel_eq_ari: for degree 1, sublevelSet = open unit disc at root
  - degree_one_rho_ge_one_ari: for degree 1, rho ≥ 1
  - degree_one_rho_le_one_ari: for degree 1, rho ≤ 1
  - degree_one_optimal_ari: for degree 1, rho = 1

  Excluded:
  - ehpConjecture — the main open problem
  - area_implies_disc_bound — requires measure theory (inscribed disc area ≤ set area)
  - clustered_implies_large_disc — requires non-trivial analysis of clustered polynomials
  - klr_better_than_pommerenke — known result but deep
  - bounds_gap — requires detailed calculation about pommerenke vs KLR bounds
-/
import Mathlib
import Proofs.Erdos1039Problem

namespace Erdos1039Aristotle

open Erdos1039 Complex Metric

-- ═══════════════════════════════════════════════════════════════════
-- PART I: Basic Properties of Inscribed Discs
-- ═══════════════════════════════════════════════════════════════════

/-- An inscribed disc has positive radius (follows directly from definition). -/
theorem isInscribedDisc_pos_ari (S : Set ℂ) (c : ℂ) (r : ℝ)
    (h : isInscribedDisc S c r) : r > 0 := h.1

/-- If r' ≤ r and disc(c, r) ⊆ S, then disc(c, r') ⊆ S too.
    A smaller disc is also inscribed. -/
theorem isInscribedDisc_mono_ari (S : Set ℂ) (c : ℂ) (r r' : ℝ)
    (hr : isInscribedDisc S c r) (hr' : r' > 0) (hrr : r' ≤ r) :
    isInscribedDisc S c r' := by
  exact ⟨hr', fun z hz => hr.2 z (lt_of_lt_of_le hz hrr)⟩

/-- The inscribed disc radius is non-negative. -/
theorem inscribedDiscRadius_nonneg_ari (S : Set ℂ) :
    inscribedDiscRadius S ≥ 0 := by
  apply Real.sSup_nonneg
  simp [inscribedDiscRadius]

/-- If r > 0 and disc(c, r) ⊆ S, then inscribedDiscRadius S ≥ r. -/
theorem inscribedDiscRadius_ge_ari (S : Set ℂ) (c : ℂ) (r : ℝ)
    (h : isInscribedDisc S c r) :
    inscribedDiscRadius S ≥ r := by
  apply Real.le_sSup
  · exact ⟨c, h⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART II: Degree-One Sublevel Set
-- ═══════════════════════════════════════════════════════════════════

/-- For a degree-1 polynomial f, the sublevel set equals the open unit disc at f.roots 0.
    Since f.eval z = z - f.roots 0, |f.eval z| < 1 iff |z - f.roots 0| < 1. -/
theorem degree_one_sublevel_eq_ari (f : UnitDiscPolynomial) (hf : f.degree = 1) :
    sublevelSet f = {z : ℂ | Complex.abs (z - f.roots ⟨0, by omega⟩) < 1} := by
  ext z
  simp only [sublevelSet, UnitDiscPolynomial.eval, Set.mem_setOf_eq]
  rw [show (Finset.univ : Finset (Fin f.degree)) = {⟨0, by omega⟩} from by
        ext i; simp [Fin.ext_iff]; omega]
  simp [Finset.prod_singleton]

/-- For degree 1, the disc of radius 1 centered at f.roots 0 is inscribed in the sublevel set.
    Proof: isInscribedDisc (sublevelSet f) (f.roots 0) 1 holds by degree_one_sublevel_eq. -/
theorem degree_one_isInscribedDisc_ari (f : UnitDiscPolynomial) (hf : f.degree = 1) :
    isInscribedDisc (sublevelSet f) (f.roots ⟨0, by omega⟩) 1 := by
  constructor
  · norm_num
  · intro z hz
    rw [degree_one_sublevel_eq_ari f hf]
    simpa using hz

/-- For degree 1, rho f ≥ 1.
    The unit disc at f.roots 0 is inscribed, so inscribedDiscRadius ≥ 1. -/
theorem degree_one_rho_ge_one_ari (f : UnitDiscPolynomial) (hf : f.degree = 1) :
    rho f ≥ 1 := by
  apply inscribedDiscRadius_ge_ari
  exact degree_one_isInscribedDisc_ari f hf

/-- For degree 1, rho f ≤ 1.
    The sublevel set is the open unit disc, which cannot contain a disc of radius > 1. -/
theorem degree_one_rho_le_one_ari (f : UnitDiscPolynomial) (hf : f.degree = 1) :
    rho f ≤ 1 := by
  sorry

/-- For degree 1, rho f = 1.
    Follows from the upper and lower bounds. -/
theorem degree_one_optimal_ari (f : UnitDiscPolynomial) (hf : f.degree = 1) :
    rho f = 1 := by
  apply le_antisymm
  · exact degree_one_rho_le_one_ari f hf
  · exact degree_one_rho_ge_one_ari f hf

-- ═══════════════════════════════════════════════════════════════════
-- PART III: Sublevel Set Properties
-- ═══════════════════════════════════════════════════════════════════

/-- The sublevel set is monotone: if S ⊆ T then inscribedDiscRadius S ≤ inscribedDiscRadius T.
    An inscribed disc in S is also inscribed in T. -/
theorem inscribedDiscRadius_mono_ari (S T : Set ℂ) (hST : S ⊆ T) :
    inscribedDiscRadius S ≤ inscribedDiscRadius T := by
  apply Real.sSup_le_sSup
  intro r ⟨c, hc⟩
  exact ⟨c, hc.1, fun z hz => hST (hc.2 z hz)⟩

/-- The benchmark polynomial zⁿ-1 has all roots on the unit circle.
    Each n-th root of unity has absolute value 1. -/
theorem rootsOfUnity_abs_ari (n : ℕ) (hn : n > 0) (i : Fin n) :
    Complex.abs ((rootsOfUnity n hn).roots i) = 1 := by
  simp [rootsOfUnity]
  rw [Complex.abs_exp_ofReal_mul_I]

end Erdos1039Aristotle
