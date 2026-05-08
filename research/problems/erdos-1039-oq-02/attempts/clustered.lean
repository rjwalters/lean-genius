/-
  Proof attempt for clustered_implies_large_disc in Erdos1039Problem.lean
  Designed by researcher-5 on 2026-05-08; build verification was blocked
  by a Mathlib cache miss (fresh git clone of mathlib4 in progress when
  the claim TTL approached). Saved here for the next researcher to drop
  into the main file and verify.

  Insertion site: replace the three `sorry` statements in
  Erdos1039Problem.lean for:
    1. (auxiliary, new) one_le_eval_of_two_le_abs / sublevelSet_subset_ball /
       bddAbove_inscribed_radii — insert as a "Sublevel Set Boundedness"
       section right after `sublevelSet_nonempty`
    2. (existing) clustered_implies_large_disc — replace the `sorry`
       with the proof body below

  Verify with: ./proofs/scripts/docker-build.sh Proofs.Erdos1039Problem
-/

-- =====================================================================
-- SECTION 1: Sublevel Set Boundedness (new infrastructure section)
-- Insert after `sublevelSet_nonempty` (around line 219) inside namespace
-- Erdos1039 with `variable (f : UnitDiscPolynomial)` in scope.
-- =====================================================================

/-- For a UnitDiscPolynomial with degree > 0, |f(z)| ≥ 1 whenever |z| ≥ 2. -/
private theorem one_le_eval_of_two_le_abs (f : UnitDiscPolynomial)
    (z : ℂ) (hz : 2 ≤ Complex.abs z) :
    1 ≤ Complex.abs (f.eval z) := by
  have h_each : ∀ i : Fin f.degree, (1 : ℝ) ≤ Complex.abs (z - f.roots i) := by
    intro i
    have hroot : Complex.abs (f.roots i) ≤ 1 := f.roots_in_disc i
    have hsum := Complex.abs.add_le (z - f.roots i) (f.roots i)
    have heq : (z - f.roots i) + f.roots i = z := by ring
    rw [heq] at hsum
    linarith
  simp only [UnitDiscPolynomial.eval, map_prod]
  calc (1 : ℝ)
      = ∏ _i : Fin f.degree, (1 : ℝ) := by rw [Finset.prod_const_one]
    _ ≤ ∏ i : Fin f.degree, Complex.abs (z - f.roots i) := by
        apply Finset.prod_le_prod
        · intro i _; exact zero_le_one
        · intro i _; exact h_each i

/-- The sublevel set of a degree-≥1 polynomial is contained in B(0, 2). -/
private theorem sublevelSet_subset_ball (f : UnitDiscPolynomial)
    (hf : 0 < f.degree) :
    sublevelSet f ⊆ Metric.ball (0 : ℂ) 2 := by
  intro z hz
  simp only [sublevelSet, Set.mem_setOf_eq] at hz
  rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
  by_contra h
  push_neg at h
  exact absurd hz (not_lt.mpr (one_le_eval_of_two_le_abs f z h))

/-- The set of inscribed-disc radii is bounded above by 4 when degree > 0. -/
private theorem bddAbove_inscribed_radii (f : UnitDiscPolynomial)
    (hf : 0 < f.degree) :
    BddAbove {r : ℝ | ∃ c : ℂ, isInscribedDisc (sublevelSet f) c r} := by
  refine ⟨4, ?_⟩
  rintro r ⟨c, hr_pos, hinscr⟩
  by_contra hgt
  push_neg at hgt
  have hr2_pos : (0 : ℝ) < r / 2 := by linarith
  let z₁ : ℂ := c + Complex.ofReal (r / 2)
  let z₂ : ℂ := c - Complex.ofReal (r / 2)
  have hsub1 : z₁ - c = Complex.ofReal (r / 2) := by
    show c + Complex.ofReal (r / 2) - c = Complex.ofReal (r / 2); ring
  have hsub2 : z₂ - c = -(Complex.ofReal (r / 2)) := by
    show c - Complex.ofReal (r / 2) - c = -(Complex.ofReal (r / 2)); ring
  have hd1 : Complex.abs (z₁ - c) < r := by
    rw [hsub1, Complex.abs_ofReal, abs_of_pos hr2_pos]
    linarith
  have hd2 : Complex.abs (z₂ - c) < r := by
    rw [hsub2, Complex.abs_neg, Complex.abs_ofReal, abs_of_pos hr2_pos]
    linarith
  have h1b := sublevelSet_subset_ball f hf (hinscr z₁ hd1)
  have h2b := sublevelSet_subset_ball f hf (hinscr z₂ hd2)
  rw [Metric.mem_ball, Complex.dist_eq, sub_zero] at h1b h2b
  have h12_sub : z₁ - z₂ = Complex.ofReal r := by
    show (c + Complex.ofReal (r / 2)) - (c - Complex.ofReal (r / 2)) = Complex.ofReal r
    rw [Complex.ofReal_div]; push_cast; ring
  have h12_abs : Complex.abs (z₁ - z₂) = r := by
    rw [h12_sub, Complex.abs_ofReal, abs_of_pos hr_pos]
  have htri : Complex.abs (z₁ - z₂) ≤ Complex.abs z₁ + Complex.abs z₂ := by
    have h := Complex.abs.add_le z₁ (-z₂)
    have heq : z₁ + (-z₂) = z₁ - z₂ := by ring
    rw [heq, Complex.abs_neg] at h
    exact h
  linarith

-- =====================================================================
-- SECTION 2: Replacement proof for `clustered_implies_large_disc`
-- =====================================================================

theorem clustered_implies_large_disc (ε : ℝ) (hε : ε > 0) (hε' : ε < 1) :
    ∀ (f : UnitDiscPolynomial), hasClusteredRoots f ε → f.degree > 0 →
      rho f ≥ 1 - ε := by
  intro f hcluster hdeg
  obtain ⟨c, hc⟩ := hcluster
  have h_inscribed : isInscribedDisc (sublevelSet f) c (1 - ε) := by
    refine ⟨by linarith, ?_⟩
    intro z hz
    simp only [sublevelSet, Set.mem_setOf_eq, UnitDiscPolynomial.eval, map_prod]
    apply Finset.prod_lt_one
    · intro i _; exact Complex.abs.nonneg _
    · intro i _
      have heq1 : z - f.roots i = (z - c) + (c - f.roots i) := by ring
      have heq2 : c - f.roots i = -(f.roots i - c) := by ring
      have h_tri : Complex.abs (z - f.roots i) ≤
          Complex.abs (z - c) + Complex.abs (f.roots i - c) := by
        rw [heq1]
        calc Complex.abs ((z - c) + (c - f.roots i))
            ≤ Complex.abs (z - c) + Complex.abs (c - f.roots i) :=
              Complex.abs.add_le _ _
          _ = Complex.abs (z - c) + Complex.abs (f.roots i - c) := by
              rw [heq2, Complex.abs_neg]
      linarith [hc i]
    · refine ⟨⟨0, hdeg⟩, Finset.mem_univ _, ?_⟩
      have heq1 : z - f.roots ⟨0, hdeg⟩ = (z - c) + (c - f.roots ⟨0, hdeg⟩) := by ring
      have heq2 : c - f.roots ⟨0, hdeg⟩ = -(f.roots ⟨0, hdeg⟩ - c) := by ring
      have h_tri : Complex.abs (z - f.roots ⟨0, hdeg⟩) ≤
          Complex.abs (z - c) + Complex.abs (f.roots ⟨0, hdeg⟩ - c) := by
        rw [heq1]
        calc Complex.abs ((z - c) + (c - f.roots ⟨0, hdeg⟩))
            ≤ Complex.abs (z - c) + Complex.abs (c - f.roots ⟨0, hdeg⟩) :=
              Complex.abs.add_le _ _
          _ = Complex.abs (z - c) + Complex.abs (f.roots ⟨0, hdeg⟩ - c) := by
              rw [heq2, Complex.abs_neg]
      linarith [hc ⟨0, hdeg⟩]
  show 1 - ε ≤ rho f
  unfold rho inscribedDiscRadius
  exact le_csSup (bddAbove_inscribed_radii f hdeg) ⟨c, h_inscribed⟩

-- =====================================================================
-- KNOWN RISKS in this draft (likely fixes for the next researcher)
-- =====================================================================
-- * `Complex.abs.add_le` — verify this dot-notation resolves to
--   `AbsoluteValue.add_le` in the current Mathlib. If not, substitute
--   with `(Complex.abs).add_le` or `AbsoluteValue.add_le Complex.abs`,
--   or convert via `‖·‖` and `norm_add_le` (using `Complex.norm_eq_abs`
--   to bridge).
-- * `Complex.abs_neg` — similarly verify; alternative is
--   `(Complex.abs).map_neg` or computing via `Complex.normSq_neg`.
-- * `unfold rho inscribedDiscRadius` — both are noncomputable defs,
--   should unfold fine. If not, try `simp only [rho, inscribedDiscRadius]`.
