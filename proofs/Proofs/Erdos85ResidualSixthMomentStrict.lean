import Proofs.Erdos85EdgeIndexedServiceSixthMomentLower
import Proofs.Erdos85OrderSixtyFourAllTwoTriangleLedger

/-! # Strict sixth-moment bound from the cubic congruence -/

open SimpleGraph Matrix Polynomial

namespace Erdos85

noncomputable section

private theorem complex_sum_powers_eq_realParts
    (s : Multiset ℂ) (m : ℕ) (hreal : ∀ z ∈ s, z.im = 0) :
    (s.map fun z ↦ z ^ m).sum =
      (((s.map Complex.re).map fun x : ℝ ↦ x ^ m).sum : ℂ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
      have hz : z.im = 0 := hreal z (by simp)
      have hs : ∀ w ∈ s, w.im = 0 := by
        intro w hw
        exact hreal w (by simp [hw])
      have hzeq : z = (z.re : ℂ) := by
        apply Complex.ext <;> simp [hz]
      have hzpow : z ^ m = ((z.re ^ m : ℝ) : ℂ) := by
        calc
          z ^ m = (z.re : ℂ) ^ m := congrArg (fun w : ℂ ↦ w ^ m) hzeq
          _ = ((z.re ^ m : ℝ) : ℂ) := (Complex.ofReal_pow _ _).symm
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [ih hs, hzpow, ← Complex.ofReal_add]

/-- If a real multiset has the h305 second and fourth moments, then its
sixth moment is strictly larger than the basic Hankel bound unless the
cubic moment is eight times the linear moment.  The proof is the identity
`Σ (x³ - 8x)² = s₆ - 16s₄ + 64s₂`. -/
theorem multiset_h305_sixthMoment_strict
    (s : Multiset ℝ)
    (h2 : (s.map fun x ↦ x ^ 2).sum = 224)
    (h4 : (s.map fun x ↦ x ^ 4).sum = 1792)
    (hcubic : (s.map fun x ↦ x ^ 3).sum ≠
      8 * (s.map fun x ↦ x).sum) :
    14336 < (s.map fun x ↦ x ^ 6).sum := by
  let L := s.toList
  have h2' : (∑ i : Fin L.length, L[i] ^ 2) = 224 := by
    have h := h2
    rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem] at h
    simpa [L] using h
  have h4' : (∑ i : Fin L.length, L[i] ^ 4) = 1792 := by
    have h := h4
    rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem] at h
    simpa [L] using h
  have hcubic' : (∑ i : Fin L.length, L[i] ^ 3) ≠
      8 * ∑ i : Fin L.length, L[i] := by
    have h := hcubic
    rw [← Multiset.sum_map_toList, ← Multiset.sum_map_toList,
      ← Fin.sum_univ_fun_getElem, ← Fin.sum_univ_fun_getElem] at h
    simpa [L] using h
  have hex : ∃ i : Fin L.length, L[i] ^ 3 - 8 * L[i] ≠ 0 := by
    by_contra h
    push Not at h
    apply hcubic'
    calc
      (∑ i : Fin L.length, L[i] ^ 3) =
          ∑ i : Fin L.length, 8 * L[i] := by
        apply Finset.sum_congr rfl
        intro i _
        exact sub_eq_zero.mp (h i)
      _ = 8 * ∑ i : Fin L.length, L[i] := by
        rw [Finset.mul_sum]
  have hpos : 0 < ∑ i : Fin L.length, (L[i] ^ 3 - 8 * L[i]) ^ 2 := by
    apply (Finset.sum_pos_iff_of_nonneg
      (fun (i : Fin L.length) _ ↦ sq_nonneg (L[i] ^ 3 - 8 * L[i]))).2
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  have h6' : (∑ i : Fin L.length, L[i] ^ 6) =
      (s.map fun x ↦ x ^ 6).sum := by
    have h : (s.map fun x ↦ x ^ 6).sum =
        ∑ i : Fin L.length, L[i] ^ 6 := by
      rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem]
      simp [L]
    exact h.symm
  have hid :
      (∑ i : Fin L.length, (L[i] ^ 3 - 8 * L[i]) ^ 2) =
        (∑ i : Fin L.length, L[i] ^ 6) -
          16 * (∑ i : Fin L.length, L[i] ^ 4) +
          64 * (∑ i : Fin L.length, L[i] ^ 2) := by
    calc
      _ = ∑ i : Fin L.length,
          (L[i] ^ 6 - 16 * L[i] ^ 4 + 64 * L[i] ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hid, h2', h4', h6'] at hpos
  norm_num at hpos ⊢
  linarith

/-- Complex Hermitian-factor form of the strict h305 residual bound. -/
theorem hermitianResidual_sixthMoment_strict
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (A : Matrix X X ℂ) (B : Matrix Y Y ℂ) (p : ℂ[X])
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hp : p ≠ 0) (hfactor : A.charpoly = p * B.charpoly)
    (h1 : complexRootPowerSum p 1 = -8)
    (h2 : complexRootPowerSum p 2 = 224)
    (h3ne : complexRootPowerSum p 3 ≠
      8 * complexRootPowerSum p 1)
    (h4 : complexRootPowerSum p 4 = 1792)
    (hB6 : Matrix.trace (B ^ 6) = 46912) :
    61248 < (Matrix.trace (A ^ 6)).re := by
  have hrootReal : ∀ z ∈ p.roots, z.im = 0 := by
    intro z hz
    have hzchar : z ∈ A.charpoly.roots := by
      rw [hfactor, roots_mul (mul_ne_zero hp B.charpoly_monic.ne_zero),
        Multiset.mem_add]
      exact Or.inl hz
    rw [hA.roots_charpoly_eq_eigenvalues] at hzchar
    obtain ⟨i, _hi, rfl⟩ := Multiset.mem_map.mp hzchar
    simp
  let s : Multiset ℝ := p.roots.map Complex.re
  have hsC (m : ℕ) : complexRootPowerSum p m =
      ((s.map fun x : ℝ ↦ x ^ m).sum : ℂ) := by
    rw [complexRootPowerSum]
    simpa [s] using complex_sum_powers_eq_realParts p.roots m hrootReal
  have hs (m : ℕ) :
      (s.map fun x ↦ x ^ m).sum = (complexRootPowerSum p m).re := by
    rw [hsC]
    exact Complex.ofReal_re _
  have hs1 : (s.map fun x ↦ x).sum = -8 := by
    have h := congrArg Complex.re h1
    rw [← hs 1] at h
    simpa using h
  have hs2 : (s.map fun x ↦ x ^ 2).sum = 224 := by
    have h := congrArg Complex.re h2
    rwa [← hs 2] at h
  have hs4 : (s.map fun x ↦ x ^ 4).sum = 1792 := by
    have h := congrArg Complex.re h4
    rwa [← hs 4] at h
  have hs3ne : (s.map fun x ↦ x ^ 3).sum ≠
      8 * (s.map fun x ↦ x).sum := by
    intro heq
    apply h3ne
    rw [hsC 3, hsC 1, heq]
    push_cast
    ring
  have hstrict := multiset_h305_sixthMoment_strict s hs2 hs4 hs3ne
  rw [hs 6] at hstrict
  have hres := residualRootPowerSum_eq_trace_sub_trace
    A B p hA hB hp hfactor 6
  have hresRe := congrArg Complex.re hres
  rw [hB6] at hresRe
  norm_num at hresRe ⊢
  linarith

/-- Graph-facing strict refinement: the cubic residual equality case is
excluded because an adjacency-cube trace is divisible by six. -/
theorem edgeIndexedService_trace_six_strict_of_eightEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (label : EightEightCycleLabeling H)
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))})
    (hEcard : Fintype.card R.edgeFinset = 48)
    (hRinj : Function.Injective (edgeEndpointSumVector R))
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ x, Cedge.degree x = 6)
    (hCfree : ¬ containsC4 R.edgeFinset Cedge) :
    61248 < (Matrix.trace ((Cedge.adjMatrix ℂ) ^ 6)).re := by
  classical
  let A := Cedge.adjMatrix ℂ
  let B := (2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ
  let I := (edgeEndpointIncidenceMatrix R).mulVecLin
  let T : Module.End ℂ (R.edgeFinset → ℂ) := A.mulVecLin
  let W := LinearMap.ker I
  let hW : W ≤ W.comap T := by
    intro x hx
    exact edgeIndexedService_incidenceKernel_invariant
      H R Cedge hservice x hx
  let p := (T.restrict hW).charpoly
  obtain ⟨hp, _hpdeg, hfactor, h1, h2, h3, h4⟩ :=
    edgeIndexedService_residual_moment_package_of_eightEight
      H R Cedge hservice label hEcard hRinj hHreg hCreg hCfree
  have h3ne : complexRootPowerSum p 3 ≠
      8 * complexRootPowerSum p 1 := by
    intro heq
    have htraceC : Matrix.trace (A ^ 3) = 160 := by
      rw [h1, h3] at heq
      norm_num at heq ⊢
      linear_combination heq
    have hcast := trace_complex_adjMatrix_pow_eq_intCast Cedge 3
    have htraceI : Matrix.trace ((Cedge.adjMatrix ℤ) ^ 3) = 160 := by
      change Matrix.trace ((Cedge.adjMatrix ℂ) ^ 3) = 160 at htraceC
      rw [hcast] at htraceC
      exact_mod_cast htraceC
    have hcard3 : 3 ≤ Fintype.card R.edgeFinset := by omega
    have htri := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount
      Cedge hcard3
    have hdiv : Matrix.trace ((Cedge.adjMatrix ℤ) ^ 3) =
        (6 : ℤ) * ((adjacencyTriangleMinorFinset Cedge).card : ℤ) := by
      simpa [pow_succ] using htri
    rw [htraceI] at hdiv
    omega
  have hAherm : A.IsHermitian :=
    SimpleGraph.isHermitian_adjMatrix ℂ Cedge
  have hBherm : B.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [B, edgeIndexedVertexOnesMatrix,
      SimpleGraph.adjMatrix_apply, H.adj_comm]
  have hB6 : Matrix.trace (B ^ 6) = 46912 := by
    simpa [B] using eightEight_centeredShore_trace_six H e hleft hright
  simpa [A] using hermitianResidual_sixthMoment_strict
    A B p hAherm hBherm hp.ne_zero hfactor h1 h2 h3ne h4 hB6

/-- The strict complex sixth-trace bound rounds up on an integer adjacency
matrix. -/
theorem trace_int_adjMatrix_pow_six_ge_61249_of_complex_strict
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hstrict : 61248 < (Matrix.trace ((G.adjMatrix ℂ) ^ 6)).re) :
    61249 ≤ Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
  have hcast := trace_complex_adjMatrix_pow_eq_intCast G 6
  rw [hcast] at hstrict
  norm_num at hstrict
  have hz : (61248 : ℤ) < Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
    exact_mod_cast hstrict
  omega

end

end Erdos85

#print axioms Erdos85.multiset_h305_sixthMoment_strict
#print axioms Erdos85.hermitianResidual_sixthMoment_strict
#print axioms Erdos85.edgeIndexedService_trace_six_strict_of_eightEight
#print axioms
  Erdos85.trace_int_adjMatrix_pow_six_ge_61249_of_complex_strict
