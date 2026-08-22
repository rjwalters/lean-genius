import Proofs.Erdos85ConnectedDesignatedTraceGrowth
import Proofs.Erdos85RationalCharpolyRootTrace
import Proofs.Erdos85RationalFactorEigenfamily
import Proofs.Erdos85ShiftedDefectEigenpair
import Proofs.Erdos85PrimarySectorExcludesDistinguishedPair

/-!
# Connected growth from a designated rational primary factor

This is the composition theorem joining the rational primary trace machinery
to the connected-nonbipartite spectral growth bound.  The full mapped root
multiset is retained, including algebraic multiplicity.
-/

open Polynomial SimpleGraph

namespace Erdos85

noncomputable section

/-- **Designated-factor growth, composed form.**  A rational designated
primary restriction of trace `-q`, whose characteristic polynomial is an
ambient Hermitian factor, produces enough paired defect eigenvalues to invoke
the connected-nonbipartite growth theorem. -/
theorem connectedNonbipartite_designatedFactor_finrank_sq_growth
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hconn : D.Connected) (hnotbip : ¬ D.IsBipartite)
    {q : ℕ} (hq : 2 ≤ q) (hreg : ∀ x, D.degree x = q - 1)
    (A T J : Matrix V V ℚ)
    (hcommM : A * T = T * A)
    (hsqM : A * A = ((q - 1 : ℕ) : ℚ) • (1 : Matrix V V ℚ) - T)
    (hJTM : J * T =
      (((q - 1 : ℕ) : ℚ) - (q * q : ℕ)) • J)
    (hD : D.adjMatrix ℚ = T + J)
    (hA : (A.map (algebraMap ℚ ℂ)).IsHermitian)
    (g : ℚ[X])
    (hgPrincipal :
      g.eval (((q - 1 : ℕ) : ℚ) - (q * q : ℕ)) ≠ 0)
    (htrace : LinearMap.trace ℚ _
      (kerAevalRestrict A.toLin' T.toLin'
        (toLin'_comm_of_matrix_comm hcommM) g) = -(q : ℚ))
    (hdiv : (kerAevalRestrict A.toLin' T.toLin'
      (toLin'_comm_of_matrix_comm hcommM) g).charpoly ∣ A.charpoly) :
    (q : ℝ) ^ 2 < 2 * ((q : ℝ) - 1) *
      (Module.finrank ℚ (LinearMap.ker (aeval T.toLin' g)) : ℝ) ^ 2 := by
  let hcomm := toLin'_comm_of_matrix_comm hcommM
  let R := kerAevalRestrict A.toLin' T.toLin' hcomm g
  let f := R.charpoly
  let roots := (f.map (algebraMap ℚ ℂ)).roots
  let L := roots.toList
  have hf : f ≠ 0 := (LinearMap.charpoly_monic R).ne_zero
  obtain ⟨θ, w, hθ, hw, hAw, hsum⟩ :=
    exists_real_eigenfamily_of_rat_charpoly_factor A hA hf hdiv
  have hrootSum : roots.sum = (-(q : ℚ) : ℂ) := by
    change (f.map (algebraMap ℚ ℂ)).roots.sum = _
    rw [sum_roots_map_charpoly_eq_trace R, htrace]
    norm_num
  have hsum' : ∑ i : Fin L.length, θ i = -(q : ℝ) := by
    rw [hsum, hrootSum]
    simp
  let AR := A.map (algebraMap ℚ ℝ)
  let TR := T.map (algebraMap ℚ ℝ)
  let JR := J.map (algebraMap ℚ ℝ)
  let castQR := algebraMap ℚ ℝ
  have hsqRM : AR * AR = ((q - 1 : ℕ) : ℝ) •
      (1 : Matrix V V ℝ) - TR := by
    have h := congrArg (fun M : Matrix V V ℚ ↦ M.map castQR) hsqM
    have hm : ((((q - 1 : ℕ) : ℚ) • (1 : Matrix V V ℚ)).map castQR) =
        ((q - 1 : ℕ) : ℝ) • (1 : Matrix V V ℝ) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [castQR, Matrix.smul_apply]
      · simp [castQR, Matrix.smul_apply, hij]
    rw [Matrix.map_sub castQR castQR.map_sub, Matrix.map_mul, hm] at h
    exact h
  have hsqR : AR.toLin' * AR.toLin' = ((q - 1 : ℕ) : ℝ) •
      (1 : (V → ℝ) →ₗ[ℝ] (V → ℝ)) - TR.toLin' := by
    have h := congrArg Matrix.toLin' hsqRM
    simpa [Module.End.mul_eq_comp, Module.End.one_eq_id] using h
  have hJTRM : JR * TR =
      (((q - 1 : ℕ) : ℝ) - (q * q : ℕ)) • JR := by
    have h := congrArg (fun M : Matrix V V ℚ ↦ M.map castQR) hJTM
    have hm : (((((q - 1 : ℕ) : ℚ) - (q * q : ℕ)) • J).map castQR) =
        (((q - 1 : ℕ) : ℝ) - (q * q : ℕ)) • JR := by
      ext i j
      simp [castQR, JR, Matrix.smul_apply]
    rw [Matrix.map_mul, hm] at h
    exact h
  have hJTR : JR.toLin' * TR.toLin' =
      (((q - 1 : ℕ) : ℝ) - (q * q : ℕ)) • JR.toLin' := by
    have h := congrArg Matrix.toLin' hJTRM
    simpa [Module.End.mul_eq_comp] using h
  have hDR : D.adjMatrix ℝ = TR + JR := by
    have h := congrArg (fun M : Matrix V V ℚ ↦ M.map castQR) hD
    have hadj : (D.adjMatrix ℚ).map castQR = D.adjMatrix ℝ := by
      ext i j
      simp [castQR, SimpleGraph.adjMatrix_apply]
    rw [Matrix.map_add castQR castQR.map_add, hadj] at h
    exact h
  let μ : Fin L.length → ℝ := fun i ↦ ((q - 1 : ℕ) : ℝ) - (θ i) ^ 2
  have hroot : ∀ i : Fin L.length, L[i] ∈ roots := by
    intro i
    rw [← Multiset.mem_toList]
    change L[i] ∈ L
    exact L.get_mem i
  have hDpair : ∀ i : Fin L.length,
      (D.adjMatrix ℝ).mulVec (w i) = μ i • w i := by
    intro i
    have hzreal := im_eq_zero_of_mem_roots_map_of_dvd_rat_charpoly
      A hA hf hdiv (hroot i)
    have hne := pair_ne_distinguished_of_mem_roots_map_primary_charpoly
      A.toLin' T.toLin' hcomm g
      (by
        have h := congrArg Matrix.toLin' hsqM
        simpa [Module.End.mul_eq_comp, Module.End.one_eq_id] using h)
      hgPrincipal
      (by
        rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
        push_cast
        ring)
      (hroot i) hzreal
    have heigen : AR.toLin' (w i) = θ i • w i := by
      simpa [AR, Matrix.toLin'_apply] using hAw i
    have hne' : ((q - 1 : ℕ) : ℝ) - (θ i) ^ 2 ≠
        ((q - 1 : ℕ) : ℝ) - (q * q : ℕ) := by
      simpa [hθ i] using hne
    have hp := shiftedDefect_eigenpair_of_adjacency_eigenpair
      AR.toLin' TR.toLin' JR.toLin' hsqR hJTR heigen hne'
    have hunshift := hp.2.2
    have hmat : (TR + JR).mulVec (w i) = μ i • w i := by
      rw [Matrix.add_mulVec]
      simpa [μ, Matrix.toLin'_apply] using hunshift
    rwa [← hDR] at hmat
  have hgrowth := connectedNonbipartite_designatedTrace_card_sq_growth
    D hconn hnotbip hq hreg Finset.univ μ θ w
    (by intro i _; exact hw i)
    (by
      intro i _ x
      have hi := congrFun (hDpair i) x
      rw [SimpleGraph.adjMatrix_mulVec_apply] at hi
      simpa [smul_eq_mul] using hi)
    (by intro i _; simp [μ])
    (by simpa using hsum')
  have hrootCard : roots.card =
      Module.finrank ℚ (LinearMap.ker (aeval T.toLin' g)) := by
    calc
      roots.card = (f.map (algebraMap ℚ ℂ)).natDegree :=
        (IsAlgClosed.splits (f.map (algebraMap ℚ ℂ))).natDegree_eq_card_roots.symm
      _ = f.natDegree :=
        Polynomial.natDegree_map_eq_of_injective
          (algebraMap ℚ ℂ).injective f
      _ = Module.finrank ℚ (LinearMap.ker (aeval T.toLin' g)) := by
        exact R.charpoly_natDegree
  have hlength : L.length =
      Module.finrank ℚ (LinearMap.ker (aeval T.toLin' g)) := by
    change roots.toList.length = _
    rw [Multiset.length_toList, hrootCard]
  simpa [hlength] using hgrowth

#print axioms connectedNonbipartite_designatedFactor_finrank_sq_growth

end

end Erdos85
