import Proofs.Erdos85UniformTraceSplitEngine

/-!
# The abstract residual trace escape

Operator form of the residual-trace vanishing theorem, freed from graph
data.  Given commuting endomorphisms `S, T` of a finite-dimensional
`ℚ`-space with `S² = κ·1 - T`, an annihilating polynomial `gP` for `T`,
and the arithmetic input that no monic irreducible divisor of `gP` other
than the designated linear sector evaluates to a square at `κ`, the trace
of `S` on any residual sector `ker r(T)` avoiding the designated sector
vanishes.

This consumes the saturated-exterior hard-sector package (`S² = 123·1-T`,
trace `-135`) against the parameter-`123` norm certificate.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- Restriction of the quadratic identity `S² = κ·1 - T` to any sector:
the `J`-free form. -/
theorem kerAevalRestrict_sq
    {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]
    (S T : E →ₗ[K] E) (hcomm : S * T = T * S) {κ : K}
    (hsq : S * S = κ • (1 : E →ₗ[K] E) - T) (g : K[X]) :
    kerAevalRestrict S T hcomm g * kerAevalRestrict S T hcomm g =
      κ • LinearMap.id - kerAevalRestrict T T rfl g := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  have hSS := LinearMap.congr_fun hsq (v : E)
  simp only [Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply] at hSS
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, AddSubgroupClass.coe_sub, SetLike.val_smul,
    kerAevalRestrict_coe]
  exact hSS

/-- **Abstract residual trace escape.**  Commuting `S, T` with
`S² = κ·1 - T`, `T` annihilated by `gP`, and every monic irreducible
divisor of `gP` other than `X - μ0` evaluating to a nonsquare at `κ`:
the trace of `S` on a residual sector `ker r(T)` with `r(μ0) ≠ 0` and
`r ∣ minpoly T` is zero. -/
theorem abstract_residual_trace_eq_zero
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (S T : E →ₗ[ℚ] E) (hcomm : S * T = T * S) {κ μ0 : ℚ}
    (hsq : S * S = κ • (1 : E →ₗ[ℚ] E) - T)
    {gP : ℚ[X]} (hgP : Polynomial.aeval T gP = 0)
    {r : ℚ[X]} (hrμ0 : r.eval μ0 ≠ 0) (hrdvd : r ∣ minpoly ℚ T)
    (harith : ∀ f : ℚ[X], f.Monic → Irreducible f → f ∣ gP →
      f ≠ X - C μ0 → ¬ IsSquare (f.eval κ)) :
    LinearMap.trace ℚ _ (kerAevalRestrict S T hcomm r) = 0 := by
  classical
  by_contra htr
  obtain ⟨f, hfirr, hfmonic, hfdvd, hfasym⟩ :=
    exists_asymmetric_factor_of_kerAevalRestrict_trace_ne_zero
      S T hcomm r htr
  have hsqSector := kerAevalRestrict_sq S T hcomm hsq r
  set Sr := kerAevalRestrict S T hcomm r with hSr
  set Tr := kerAevalRestrict T T rfl r with hTr
  set bb := Module.Free.chooseBasis ℚ
    (LinearMap.ker (Polynomial.aeval T r)) with hbb
  set M := LinearMap.toMatrix bb bb Sr with hM
  set N := LinearMap.toMatrix bb bb Tr with hN
  have hMcharpoly : M.charpoly = Sr.charpoly :=
    LinearMap.charpoly_toMatrix Sr bb
  have hfdvdM : f ∣ M.charpoly := by rw [hMcharpoly]; exact hfdvd
  haveI hNE : Nonempty (Module.Free.ChooseBasisIndex ℚ
      (LinearMap.ker (Polynomial.aeval T r))) := by
    rw [← Fintype.card_pos_iff]
    by_contra h0
    have hdeg0 : M.charpoly.natDegree = 0 := by
      rw [Matrix.charpoly_natDegree_eq_dim]
      omega
    have hone : M.charpoly = 1 :=
      (Matrix.charpoly_monic M).natDegree_eq_zero.mp hdeg0
    rw [hone] at hfdvdM
    exact hfirr.not_isUnit (isUnit_of_dvd_one hfdvdM)
  have hfmapdeg : (f.map (algebraMap ℚ (AlgebraicClosure ℚ))).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective
      (algebraMap ℚ (AlgebraicClosure ℚ)).injective]
    exact (Polynomial.degree_pos_of_irreducible hfirr).ne'
  obtain ⟨θ, hθroot'⟩ := IsAlgClosed.exists_root _ hfmapdeg
  have hθf : Polynomial.aeval θ f = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.eval_map] using hθroot'.eq_zero
  have hθchar : Polynomial.aeval θ M.charpoly = 0 := by
    obtain ⟨q, hq⟩ := hfdvdM
    rw [hq, map_mul, hθf, zero_mul]
  obtain ⟨u, hu0, hMu⟩ :=
    matrix_exists_eigenvector_of_aeval_charpoly_eq_zero M θ hθchar
  have hMN : M * M = κ • (1 : Matrix _ _ ℚ) - N := by
    have h := congrArg (LinearMap.toMatrix bb bb) hsqSector
    rwa [LinearMap.toMatrix_mul, map_sub (LinearMap.toMatrix bb bb),
      map_smul (LinearMap.toMatrix bb bb), LinearMap.toMatrix_id] at h
  set φ := algebraMap ℚ (AlgebraicClosure ℚ) with hφ
  set μ : AlgebraicClosure ℚ := ((κ : ℚ) : AlgebraicClosure ℚ) - θ ^ 2
    with hμdef
  have hNmap : N.map φ =
      (((κ : ℚ) : AlgebraicClosure ℚ)) •
        (1 : Matrix _ _ (AlgebraicClosure ℚ)) - (M.map φ) * (M.map φ) := by
    have hNeq : N = κ • (1 : Matrix _ _ ℚ) - M * M := by
      rw [hMN, sub_sub_cancel]
    rw [hNeq, Matrix.map_sub, Matrix.map_mul]
    congr 1
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one]
      exact eq_ratCast φ κ
    · simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_ne h,
        smul_eq_mul, mul_zero, map_zero]
    · exact fun a b => map_sub φ a b
  have hNu : (N.map φ).mulVec u = μ • u := by
    rw [hNmap, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hMu, Matrix.mulVec_smul, hMu, smul_smul,
      hμdef, sub_smul, pow_two]
  have hTrann : Polynomial.aeval Tr r = 0 := by
    rw [hTr]
    exact aeval_kerAevalRestrict_self _ r
  have hNr : Polynomial.aeval N r = 0 := by
    rw [hN, ← toMatrix_aeval, hTrann, map_zero]
  have hNr' : Polynomial.aeval (N.map φ) r = 0 := by
    have h := Polynomial.aeval_algHom_apply
      ((Algebra.ofId ℚ (AlgebraicClosure ℚ)).mapMatrix) N r
    rw [hNr, map_zero] at h
    have hmm : (Algebra.ofId ℚ (AlgebraicClosure ℚ)).mapMatrix N =
        N.map φ := by
      ext i j
      simp [AlgHom.mapMatrix_apply, Matrix.map_apply, hφ, Algebra.ofId_apply]
    rwa [hmm] at h
  have hμr : Polynomial.aeval μ r = 0 :=
    matrix_aeval_eq_zero_of_eigenvector_of_aeval_matrix_eq_zero
      (N.map φ) hu0 hNu hNr'
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  have hμint : IsIntegral ℚ μ :=
    (Algebra.IsAlgebraic.isAlgebraic μ).isIntegral
  have hmindvd_r : minpoly ℚ μ ∣ r := minpoly.dvd ℚ μ hμr
  have hmindvd_gP : minpoly ℚ T ∣ gP := minpoly.dvd ℚ T hgP
  have hminμ_dvd_gP : minpoly ℚ μ ∣ gP :=
    dvd_trans (dvd_trans hmindvd_r hrdvd) hmindvd_gP
  have hfμne : minpoly ℚ μ ≠ X - C μ0 := by
    intro heq
    have hroot : Polynomial.aeval μ (X - C μ0) = 0 := by
      rw [← heq]
      exact minpoly.aeval ℚ μ
    have hμeq : μ = algebraMap ℚ (AlgebraicClosure ℚ) μ0 := by
      have hsub : μ - algebraMap ℚ (AlgebraicClosure ℚ) μ0 = 0 := by
        simpa using hroot
      exact sub_eq_zero.mp hsub
    rw [hμeq, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at hμr
    exact hrμ0 ((algebraMap ℚ (AlgebraicClosure ℚ)).injective
      (by simpa using hμr))
  have hvalue : ¬ IsSquare ((minpoly ℚ μ).eval κ) :=
    harith (minpoly ℚ μ) (minpoly.monic hμint)
      (minpoly.irreducible hμint) hminμ_dvd_gP hfμne
  have hμform : μ = ((κ : ℚ) : AlgebraicClosure ℚ) - θ ^ 2 := hμdef
  obtain ⟨tt, httmem, httsq⟩ := exists_sq_root_of_asymmetric_factor
    κ f hfirr hfmonic hfasym θ hθf μ hμform
  exact not_exists_sq_root_of_minpoly_eval_not_isSquare μ κ
    hμint hvalue ⟨tt, httmem, httsq⟩

end

end Erdos85
