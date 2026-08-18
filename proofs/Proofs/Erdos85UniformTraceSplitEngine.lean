import Proofs.Erdos85PrincipalIndicatorTrace
import Proofs.Erdos85GlobalCycleFactorization
import Proofs.Erdos85AdjoinNormMinpoly
import Proofs.Erdos85DistanceLayers

/-!
# The uniform trace-split kill engine

For an even plateau degree `d ≥ 4` whose conductor table contains exactly
one square — the designated rational sector `μ₀` with
`d - 1 - μ₀ = t²`, `t ∤ d` — a hypothetical `C₄`-free graph of minimum
degree `d` on the exact boundary order `d(d-1)+3` is destroyed by the
three-sector primary trace split:

* the defect operator is annihilated by `(X-2)(X-μ₀)·r` with pairwise
  coprime factors (symmetric sector factorization);
* the principal sector `ker (T - 2)` carries trace `d` (indicator basis
  plus the positive-excess weighted quotient identity, using that `d-3`
  is nonsquare);
* the residual sector has trace zero: otherwise an asymmetric irreducible
  factor of its charpoly produces an eigenvalue `μ = d-1-θ²` of the
  defect cycles with `θ ∈ ℚ(μ)`, so `d-1-μ` is a square in `ℚ(μ)`,
  contradicting the arithmetic certificate that every non-designated
  conductor value is nonsquare;
* the total adjacency trace vanishes, so the unique square sector must
  carry trace `-d`, forcing `t ∣ d` — a contradiction.

The arithmetic certificate is consumed through the hypothesis `harith`,
discharged per degree by the executable norm-certificate chain.
-/

open Polynomial
open scoped Matrix

namespace Erdos85

open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restriction of the quadratic identity `S² = κ·1 + J - T` to any sector
killed by `J`. -/
theorem kerAevalRestrict_sq_of_eval_ne_zero
    {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]
    (S T J : E →ₗ[K] E) (hcomm : S * T = T * S) {κ δ : K}
    (hsq : S * S = κ • (1 : E →ₗ[K] E) + J - T)
    (hJT : J * T = δ • J) {g : K[X]} (hg : g.eval δ ≠ 0) :
    kerAevalRestrict S T hcomm g * kerAevalRestrict S T hcomm g =
      κ • LinearMap.id - kerAevalRestrict T T rfl g := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  have hJv : J (v : E) = 0 :=
    apply_eq_zero_of_mem_ker_aeval_of_eval_ne_zero J T hJT hg (v : E) v.2
  have hSS := LinearMap.congr_fun hsq (v : E)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply] at hSS
  rw [hJv, add_zero] at hSS
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, AddSubgroupClass.coe_sub, SetLike.val_smul,
    kerAevalRestrict_coe]
  exact hSS

/-- `toMatrix` transports powers. -/
theorem toMatrix_pow {W : Type*} [AddCommGroup W] [Module ℚ W]
    {n : Type*} [Fintype n] [DecidableEq n] (bb : Module.Basis n ℚ W)
    (g : W →ₗ[ℚ] W) (m : ℕ) :
    LinearMap.toMatrix bb bb (g ^ m) = (LinearMap.toMatrix bb bb g) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ, LinearMap.toMatrix_mul, ih]

/-- `toMatrix` transports polynomial evaluation. -/
theorem toMatrix_aeval {W : Type*} [AddCommGroup W] [Module ℚ W]
    {n : Type*} [Fintype n] [DecidableEq n] (bb : Module.Basis n ℚ W)
    (g : W →ₗ[ℚ] W) (p : ℚ[X]) :
    LinearMap.toMatrix bb bb (Polynomial.aeval g p) =
      Polynomial.aeval (LinearMap.toMatrix bb bb g) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | monomial m a =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        LinearMap.toMatrix_mul, toMatrix_pow]
      congr 1
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        map_smul, LinearMap.toMatrix_one]

/-- The defect charpoly factors through the component cycle Chebyshev
polynomials. -/
theorem secondOrderDefect_adjMatrix_charpoly_eq_prod_chebyshev
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree) (hcard : Fintype.card V = d * (d - 1) + 3) :
    (∀ c : (secondOrderDefectGraph G).ConnectedComponent,
        3 ≤ c.supp.ncard) ∧
      ((secondOrderDefectGraph G).adjMatrix ℤ).charpoly =
        ∏ c : (secondOrderDefectGraph G).ConnectedComponent,
          (Polynomial.Chebyshev.C ℤ (c.supp.ncard : ℤ) - 2) := by
  constructor
  · intro c
    obtain ⟨r, hr3, hrsize, -⟩ :=
      secondOrderDefect_resolvent_eq_prod_chebyshev
        G hfree hd heven hmin hcard 0
    rw [← hrsize c]
    exact hr3 c
  · apply Polynomial.funext
    intro a
    obtain ⟨r, hr3, hrsize, hdet⟩ :=
      secondOrderDefect_resolvent_eq_prod_chebyshev
        G hfree hd heven hmin hcard a
    rw [Matrix.eval_charpoly, hdet, Polynomial.eval_prod]
    exact Finset.prod_congr rfl fun c _ => by rw [hrsize c]

set_option maxHeartbeats 1600000 in
/-- **Residual trace vanishing.**  If every non-designated conductor value
is nonsquare, the residual sector of the trace split carries trace zero. -/
theorem residual_trace_eq_zero
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree) (hcard : Fintype.card V = d * (d - 1) + 3)
    (hreg : ∀ x, G.degree x = d) {μ0 : ℚ}
    (harith : ∀ n : ℕ, 3 ≤ n → n ≤ Fintype.card V →
      ∀ f : Polynomial ℚ, f.Monic → Irreducible f →
        f ∣ (Polynomial.Chebyshev.C ℤ (n : ℤ) - 2).map (algebraMap ℤ ℚ) →
        f ≠ X - C μ0 → ¬ IsSquare (f.eval ((d : ℚ) - 1)))
    (hcommQ : Matrix.toLin' (G.adjMatrix ℚ) *
        Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ) =
      Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ) *
        Matrix.toLin' (G.adjMatrix ℚ))
    (hsqE : Matrix.toLin' (G.adjMatrix ℚ) * Matrix.toLin' (G.adjMatrix ℚ) =
      ((d : ℚ) - 1) • (1 : (V → ℚ) →ₗ[ℚ] (V → ℚ)) +
        Matrix.toLin' (ratOnesMatrix V) -
        Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ))
    (hJTE : Matrix.toLin' (ratOnesMatrix V) *
        Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ) =
      (2 : ℚ) • Matrix.toLin' (ratOnesMatrix V))
    {r : ℚ[X]} (hr2 : r.eval 2 ≠ 0) (hrμ0 : r.eval μ0 ≠ 0)
    (hrdvd : r ∣ minpoly ℚ ((secondOrderDefectGraph G).adjMatrix ℚ)) :
    LinearMap.trace ℚ _
      (kerAevalRestrict (Matrix.toLin' (G.adjMatrix ℚ))
        (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ))
        hcommQ r) = 0 := by
  classical
  by_contra htr
  obtain ⟨f, hfirr, hfmonic, hfdvd, hfasym⟩ :=
    exists_asymmetric_factor_of_kerAevalRestrict_trace_ne_zero
      (Matrix.toLin' (G.adjMatrix ℚ))
      (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ)) hcommQ r htr
  -- the sector square identity
  have hsqSector := kerAevalRestrict_sq_of_eval_ne_zero
    (Matrix.toLin' (G.adjMatrix ℚ))
    (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ))
    (Matrix.toLin' (ratOnesMatrix V)) hcommQ hsqE hJTE hr2
  -- coordinates on the residual sector
  set Sr := kerAevalRestrict (Matrix.toLin' (G.adjMatrix ℚ))
    (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ)) hcommQ r
    with hSr
  set Tr := kerAevalRestrict
    (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ))
    (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ)) rfl r with hTr
  set bb := Module.Free.chooseBasis ℚ
    (LinearMap.ker (Polynomial.aeval
      (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ)) r)) with hbb
  set M := LinearMap.toMatrix bb bb Sr with hM
  set N := LinearMap.toMatrix bb bb Tr with hN
  have hMcharpoly : M.charpoly = Sr.charpoly :=
    LinearMap.charpoly_toMatrix Sr bb
  have hfdvdM : f ∣ M.charpoly := by rw [hMcharpoly]; exact hfdvd
  haveI hNE : Nonempty (Module.Free.ChooseBasisIndex ℚ
      (LinearMap.ker (Polynomial.aeval
        (Matrix.toLin' ((secondOrderDefectGraph G).adjMatrix ℚ)) r))) := by
    rw [← Fintype.card_pos_iff]
    by_contra h0
    have hdeg0 : M.charpoly.natDegree = 0 := by
      rw [Matrix.charpoly_natDegree_eq_dim]
      omega
    have hone : M.charpoly = 1 :=
      (Matrix.charpoly_monic M).natDegree_eq_zero.mp hdeg0
    rw [hone] at hfdvdM
    exact hfirr.not_isUnit (isUnit_of_dvd_one hfdvdM)
  -- a root of the asymmetric factor
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
  -- the matrix square identity
  have hMN : M * M = ((d : ℚ) - 1) • (1 : Matrix _ _ ℚ) - N := by
    have h := congrArg (LinearMap.toMatrix bb bb) hsqSector
    rwa [LinearMap.toMatrix_mul, map_sub (LinearMap.toMatrix bb bb),
      map_smul (LinearMap.toMatrix bb bb), LinearMap.toMatrix_id] at h
  -- transport to the closure and read off the defect eigenvalue
  set φ := algebraMap ℚ (AlgebraicClosure ℚ) with hφ
  set μ : AlgebraicClosure ℚ :=
    (((d : ℚ) - 1 : ℚ) : AlgebraicClosure ℚ) - θ ^ 2 with hμdef
  have hNmap : N.map φ =
      ((((d : ℚ) - 1 : ℚ) : AlgebraicClosure ℚ)) •
        (1 : Matrix _ _ (AlgebraicClosure ℚ)) - (M.map φ) * (M.map φ) := by
    have hNeq : N = ((d : ℚ) - 1) • (1 : Matrix _ _ ℚ) - M * M := by
      rw [hMN, sub_sub_cancel]
    rw [hNeq, Matrix.map_sub, Matrix.map_mul]
    congr 1
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one]
      exact eq_ratCast φ ((d : ℚ) - 1)
    · simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_ne h,
        smul_eq_mul, mul_zero, map_zero]
    · exact fun a b => map_sub φ a b
  have hNu : (N.map φ).mulVec u = μ • u := by
    rw [hNmap, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hMu, Matrix.mulVec_smul, hMu, smul_smul,
      hμdef, sub_smul, pow_two]
  -- μ is a root of the residual polynomial
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
  -- minimal polynomial of μ divides one cycle Chebyshev factor
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  have hμint : IsIntegral ℚ μ :=
    (Algebra.IsAlgebraic.isAlgebraic μ).isIntegral
  have hmindvd_r : minpoly ℚ μ ∣ r := minpoly.dvd ℚ μ hμr
  have hmindvd_char :
      minpoly ℚ ((secondOrderDefectGraph G).adjMatrix ℚ) ∣
        ((secondOrderDefectGraph G).adjMatrix ℚ).charpoly :=
    minpoly.dvd ℚ _ (Matrix.aeval_self_charpoly _)
  obtain ⟨hlen3, hcharfac⟩ :=
    secondOrderDefect_adjMatrix_charpoly_eq_prod_chebyshev
      G hfree hd heven hmin hcard
  have hcharQ : ((secondOrderDefectGraph G).adjMatrix ℚ).charpoly =
      ∏ c : (secondOrderDefectGraph G).ConnectedComponent,
        ((Polynomial.Chebyshev.C ℤ (c.supp.ncard : ℤ) - 2).map
          (algebraMap ℤ ℚ)) := by
    calc ((secondOrderDefectGraph G).adjMatrix ℚ).charpoly
        = ((((secondOrderDefectGraph G).adjMatrix ℤ).map
            (Int.castRingHom ℚ)).charpoly) := by
          rw [adjMatrix_map_intCast]
      _ = (((secondOrderDefectGraph G).adjMatrix ℤ).charpoly).map
            (Int.castRingHom ℚ) := Matrix.charpoly_map _ _
      _ = (∏ c : (secondOrderDefectGraph G).ConnectedComponent,
            (Polynomial.Chebyshev.C ℤ (c.supp.ncard : ℤ) - 2)).map
            (Int.castRingHom ℚ) := by rw [hcharfac]
      _ = ∏ c : (secondOrderDefectGraph G).ConnectedComponent,
            ((Polynomial.Chebyshev.C ℤ (c.supp.ncard : ℤ) - 2).map
              (algebraMap ℤ ℚ)) := by
          rw [Polynomial.map_prod]
          exact Finset.prod_congr rfl fun c _ => by rw [algebraMap_int_eq]
  have hminμ_dvd_prod : minpoly ℚ μ ∣
      ∏ c : (secondOrderDefectGraph G).ConnectedComponent,
        ((Polynomial.Chebyshev.C ℤ (c.supp.ncard : ℤ) - 2).map
          (algebraMap ℤ ℚ)) := by
    rw [← hcharQ]
    exact dvd_trans (dvd_trans hmindvd_r hrdvd) hmindvd_char
  have hprime : Prime (minpoly ℚ μ) :=
    (UniqueFactorizationMonoid.irreducible_iff_prime).mp
      (minpoly.irreducible hμint)
  obtain ⟨c0, -, hdvdc0⟩ :=
    hprime.exists_mem_finset_dvd hminμ_dvd_prod
  -- bounds for the certificate
  have hlenle : c0.supp.ncard ≤ Fintype.card V := by
    have := Set.ncard_le_ncard (Set.subset_univ c0.supp) Set.finite_univ
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  -- the designated sector is excluded by coprimality
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
  have hvalue : ¬ IsSquare ((minpoly ℚ μ).eval ((d : ℚ) - 1)) :=
    harith c0.supp.ncard (hlen3 c0) hlenle (minpoly ℚ μ)
      (minpoly.monic hμint) (minpoly.irreducible hμint) hdvdc0 hfμne
  -- the asymmetric factor manufactures a square root in ℚ(μ)
  have hμform : μ = (((d : ℚ) - 1 : ℚ) : AlgebraicClosure ℚ) - θ ^ 2 :=
    hμdef
  obtain ⟨tt, httmem, httsq⟩ := exists_sq_root_of_asymmetric_factor
    ((d : ℚ) - 1) f hfirr hfmonic hfasym θ hθf μ hμform
  exact not_exists_sq_root_of_minpoly_eval_not_isSquare μ ((d : ℚ) - 1)
    hμint hvalue ⟨tt, httmem, httsq⟩

end

end Erdos85
