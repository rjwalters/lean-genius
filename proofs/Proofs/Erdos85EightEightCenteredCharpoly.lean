import Proofs.Erdos85MuNegThreeZeroFiveIrrationalEigenfamilies
import Proofs.Erdos85MuNegThreeZeroFiveExplicitEigenfamilies
import Proofs.Erdos85EdgeIndexedServiceQuotientOperator

/-! # Exact characteristic polynomial of the centered C8 plus C8 operator -/

open Finset SimpleGraph Matrix Polynomial

namespace Erdos85

noncomputable section

private theorem centeredShore_mulVec_of_sum_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (f : V → ℂ) (mu : ℂ)
    (hsum : ∑ x, f x = 0)
    (heig : (H.adjMatrix ℂ).mulVec f = mu • f) :
    ((2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ).mulVec f =
      (-mu) • f := by
  funext x
  have hj : (edgeIndexedVertexOnesMatrix V).mulVec f x = 0 := by
    simp [edgeIndexedVertexOnesMatrix, Matrix.mulVec, dotProduct, hsum]
  have he := congrFun heig x
  simp [Matrix.sub_mulVec, Matrix.smul_mulVec, hj, he]

private def centeredConstantFamily
    (V : Type*) : Fin 1 → V → ℂ := fun _ _ ↦ 1

private theorem centeredConstantFamily_linearIndependent
    {V : Type*} [Fintype V] [Nonempty V] :
    LinearIndependent ℂ (centeredConstantFamily V) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have hq : q = 0 := Subsingleton.elim _ _
  subst q
  let x : V := Classical.choice (inferInstance : Nonempty V)
  have h := congrFun hg x
  simpa [centeredConstantFamily] using h

private theorem centeredConstantFamily_eigenvalue_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V = 16)
    (hreg : ∀ x, H.degree x = 2) :
    ∀ q, ((2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ).mulVec
      (centeredConstantFamily V q) =
        (6 : ℂ) • centeredConstantFamily V q := by
  intro q
  funext x
  have hJ : (edgeIndexedVertexOnesMatrix V).mulVec
      (centeredConstantFamily V q) x = (16 : ℂ) := by
    simp [centeredConstantFamily, edgeIndexedVertexOnesMatrix,
      Matrix.mulVec, dotProduct, hcard]
  have hA : (H.adjMatrix ℂ).mulVec
      (centeredConstantFamily V q) x = (2 : ℂ) := by
    simpa [centeredConstantFamily, hreg] using
      (H.adjMatrix_mulVec_const_apply (R := ℂ) (a := (1 : ℂ)) (v := x))
  simp [Matrix.sub_mulVec, Matrix.smul_mulVec, hJ, hA,
    centeredConstantFamily]
  norm_num

/-- The displayed degree-sixteen polynomial divides the centered shore
characteristic polynomial. -/
theorem eightEight_centeredCharpoly_candidate_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))}) :
    let B := (2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ
    (X - C (6 : ℂ)) * (X - C (-2 : ℂ)) *
      (X - C (2 : ℂ)) ^ 2 * X ^ 4 *
      (X - C ((Real.sqrt 2 : ℝ) : ℂ)) ^ 4 *
      (X - C (-((Real.sqrt 2 : ℝ) : ℂ))) ^ 4 ∣ B.charpoly := by
  classical
  dsimp only
  let B := (2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ
  have hcard : Fintype.card V = 16 := by
    rw [← Fintype.card_congr e]
    decide
  have hreg : ∀ x, H.degree x = 2 := by
    intro x
    obtain ⟨i | i, rfl⟩ := e.surjective x
    · rw [← H.card_neighborFinset_eq_degree, hleft]
      simp [h305_cycle_neighbor_coordinates_ne]
    · rw [← H.card_neighborFinset_eq_degree, hright]
      simp [h305_cycle_neighbor_coordinates_ne]
  letI : Nonempty V := ⟨e (Sum.inl 0)⟩
  let fzero : Fin 4 → V → ℂ := fun q ↦
    h305ZeroEigenfamily e (finProdFinEquiv.symm q)
  have h6 : (X - C (6 : ℂ)) ^ 1 ∣ B.charpoly :=
    matrix_charpoly_linearFactor_pow_dvd_of_eigenfamily B 6 1
      (centeredConstantFamily V)
      (centeredConstantFamily_eigenvalue_six H hcard hreg)
      centeredConstantFamily_linearIndependent
  have hzero : (X - C (0 : ℂ)) ^ 4 ∣ B.charpoly :=
    matrix_charpoly_linearFactor_pow_dvd_of_eigenfamily B 0 4
      fzero
      (fun q ↦ by
        simpa [B, fzero] using
          (centeredShore_mulVec_of_sum_zero H _ 0
            (h305_zeroEigenfamily_sum_zero e (finProdFinEquiv.symm q))
            (h305_zeroEigenfamily_eigenvalue_zero H e hleft hright
              (finProdFinEquiv.symm q))))
      ((h305_zeroEigenfamily_linearIndependent e).comp _
        finProdFinEquiv.symm.injective)
  have h2 : (X - C (2 : ℂ)) ^ 2 ∣ B.charpoly :=
    matrix_charpoly_linearFactor_pow_dvd_of_eigenfamily B 2 2
      (h305AlternatingEigenfamily e)
      (fun q ↦ by
        simpa only [neg_neg] using
          (centeredShore_mulVec_of_sum_zero H _ (-2)
            (h305_alternatingEigenfamily_sum_zero e q)
            (h305_alternatingEigenfamily_eigenvalue_neg_two
              H e hleft hright q)))
      (h305_alternatingEigenfamily_linearIndependent e)
  have hm2 : (X - C (-2 : ℂ)) ^ 1 ∣ B.charpoly :=
    matrix_charpoly_linearFactor_pow_dvd_of_eigenfamily B (-2) 1
      (h305ShoreDifferenceFamily e)
      (fun q ↦ centeredShore_mulVec_of_sum_zero H _ 2
        (h305_shoreDifference_sum_zero e)
        (h305_shoreDifference_eigenvalue_two H e hleft hright))
      (h305_shoreDifferenceFamily_linearIndependent e)
  have hsqrt (neg : Fin 2) :
      let mu : ℂ := ((if neg = 0 then Real.sqrt 2 else -Real.sqrt 2 : ℝ) : ℂ)
      (X - C (-mu)) ^ 4 ∣ B.charpoly := by
    dsimp only
    let fsqrt : Fin 4 → V → ℂ := fun q ↦
      h305SqrtTwoEigenfamily e neg (finProdFinEquiv.symm q)
    apply matrix_charpoly_linearFactor_pow_dvd_of_eigenfamily B _ 4
      fsqrt
    · intro q
      simpa [B, fsqrt] using
        (centeredShore_mulVec_of_sum_zero H _ _
          (h305_sqrtTwoEigenfamily_sum_zero e neg (finProdFinEquiv.symm q))
          (h305_sqrtTwoEigenfamily_eigenvalue H e hleft hright neg
            (finProdFinEquiv.symm q)))
    · exact (h305_sqrtTwoEigenfamily_linearIndependent e neg).comp _
        finProdFinEquiv.symm.injective
  have hspos : (X - C (((Real.sqrt 2 : ℝ) : ℂ))) ^ 4 ∣ B.charpoly := by
    simpa using hsqrt (1 : Fin 2)
  have hsneg : (X - C (-((Real.sqrt 2 : ℝ) : ℂ))) ^ 4 ∣ B.charpoly := by
    simpa using hsqrt (0 : Fin 2)
  let s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
  have hs2 : s ^ 2 = 2 := by
    change (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsne (r : ℂ) (hr : r ^ 2 ≠ 2) : s ≠ r := by
    intro h
    apply hr
    simpa [h] using hs2
  have hs0 : s ≠ 0 := hsne 0 (by norm_num)
  have hs6 : s ≠ 6 := hsne 6 (by norm_num)
  have hs2c : s ≠ 2 := hsne 2 (by norm_num)
  have hsm2 : s ≠ -2 := hsne (-2) (by norm_num)
  have hns0 : -s ≠ 0 := neg_ne_zero.mpr hs0
  have hns6 : -s ≠ 6 := by
    intro h
    apply hsne (-6) (by norm_num)
    simpa using congrArg Neg.neg h
  have hns2 : -s ≠ 2 := by
    intro h
    apply hsne (-2) (by norm_num)
    simpa using congrArg Neg.neg h
  have hnsm2 : -s ≠ -2 := by
    intro h
    apply hsne 2 (by norm_num)
    simpa using congrArg Neg.neg h
  have hsns : s ≠ -s := by
    intro h
    apply hs0
    have hz : (2 : ℂ) * s = 0 := by linear_combination h
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  have hcop (a b : ℂ) (hab : a ≠ b) (m n : ℕ) :
      IsCoprime ((X - C a) ^ m) ((X - C b) ^ n) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hab).isUnit).pow
  let f6 := (X - C (6 : ℂ)) ^ 1
  let fm2 := (X - C (-2 : ℂ)) ^ 1
  let f2 := (X - C (2 : ℂ)) ^ 2
  let f0 := (X - C (0 : ℂ)) ^ 4
  let fs := (X - C s) ^ 4
  let fns := (X - C (-s)) ^ 4
  have hc6m2 : IsCoprime f6 fm2 := hcop 6 (-2) (by norm_num) 1 1
  have hd6m2 : f6 * fm2 ∣ B.charpoly := hc6m2.mul_dvd h6 hm2
  have hc6_2 : IsCoprime f6 f2 := hcop 6 2 (by norm_num) 1 2
  have hcm2_2 : IsCoprime fm2 f2 := hcop (-2) 2 (by norm_num) 1 2
  have hc62_2 : IsCoprime (f6 * fm2) f2 := hc6_2.mul_left hcm2_2
  have hd2 : f6 * fm2 * f2 ∣ B.charpoly := hc62_2.mul_dvd hd6m2 h2
  have hc6_0 : IsCoprime f6 f0 := hcop 6 0 (by norm_num) 1 4
  have hcm2_0 : IsCoprime fm2 f0 := hcop (-2) 0 (by norm_num) 1 4
  have hc2_0 : IsCoprime f2 f0 := hcop 2 0 (by norm_num) 2 4
  have hc620 : IsCoprime (f6 * fm2 * f2) f0 :=
    (hc6_0.mul_left hcm2_0).mul_left hc2_0
  have hd0 : f6 * fm2 * f2 * f0 ∣ B.charpoly :=
    hc620.mul_dvd hd2 hzero
  have hc6_s : IsCoprime f6 fs := hcop 6 s hs6.symm 1 4
  have hcm2_s : IsCoprime fm2 fs := hcop (-2) s hsm2.symm 1 4
  have hc2_s : IsCoprime f2 fs := hcop 2 s hs2c.symm 2 4
  have hc0_s : IsCoprime f0 fs := hcop 0 s hs0.symm 4 4
  have hc620s : IsCoprime (f6 * fm2 * f2 * f0) fs :=
    ((hc6_s.mul_left hcm2_s).mul_left hc2_s).mul_left hc0_s
  have hds : f6 * fm2 * f2 * f0 * fs ∣ B.charpoly :=
    hc620s.mul_dvd hd0 (by simpa [fs, s] using hspos)
  have hc6_ns : IsCoprime f6 fns := hcop 6 (-s) hns6.symm 1 4
  have hcm2_ns : IsCoprime fm2 fns := hcop (-2) (-s) hnsm2.symm 1 4
  have hc2_ns : IsCoprime f2 fns := hcop 2 (-s) hns2.symm 2 4
  have hc0_ns : IsCoprime f0 fns := hcop 0 (-s) hns0.symm 4 4
  have hcs_ns : IsCoprime fs fns := hcop s (-s) hsns 4 4
  have hcall : IsCoprime (f6 * fm2 * f2 * f0 * fs) fns :=
    (((hc6_ns.mul_left hcm2_ns).mul_left hc2_ns).mul_left hc0_ns).mul_left hcs_ns
  have hdall : f6 * fm2 * f2 * f0 * fs * fns ∣ B.charpoly :=
    hcall.mul_dvd hds (by simpa [fns, s] using hsneg)
  simpa [f6, fm2, f2, f0, fs, fns, s, pow_one] using hdall

/-- Exact centered quotient characteristic polynomial for two labeled
eight-cycles. -/
theorem eightEight_centeredCharpoly_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))}) :
    let B := (2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ
    B.charpoly =
      (X - C (6 : ℂ)) * (X - C (-2 : ℂ)) *
        (X - C (2 : ℂ)) ^ 2 * X ^ 4 *
        (X - C ((Real.sqrt 2 : ℝ) : ℂ)) ^ 4 *
        (X - C (-((Real.sqrt 2 : ℝ) : ℂ))) ^ 4 := by
  classical
  dsimp only
  let B := (2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ
  let q : ℂ[X] :=
    (X - C (6 : ℂ)) * (X - C (-2 : ℂ)) *
      (X - C (2 : ℂ)) ^ 2 * X ^ 4 *
      (X - C ((Real.sqrt 2 : ℝ) : ℂ)) ^ 4 *
      (X - C (-((Real.sqrt 2 : ℝ) : ℂ))) ^ 4
  change B.charpoly = q
  have hdvd : q ∣ B.charpoly := by
    simpa [q, B] using
      eightEight_centeredCharpoly_candidate_dvd H e hleft hright
  have hqmonic : q.Monic := by
    dsimp [q]
    exact (((((monic_X_sub_C (6 : ℂ)).mul
      (monic_X_sub_C (-2 : ℂ))).mul
      ((monic_X_sub_C (2 : ℂ)).pow 2)).mul (monic_X.pow 4)).mul
      ((monic_X_sub_C (((Real.sqrt 2 : ℝ) : ℂ))).pow 4)).mul
      ((monic_X_sub_C (-((Real.sqrt 2 : ℝ) : ℂ))).pow 4)
  have hqdeg : q.natDegree = 16 := by
    let p6 : ℂ[X] := X - C 6
    let pm2 : ℂ[X] := X - C (-2)
    let p2 : ℂ[X] := (X - C 2) ^ 2
    let p0 : ℂ[X] := X ^ 4
    let ps : ℂ[X] := (X - C ((Real.sqrt 2 : ℝ) : ℂ)) ^ 4
    let pns : ℂ[X] := (X - C (-((Real.sqrt 2 : ℝ) : ℂ))) ^ 4
    let m6 : p6.Monic := monic_X_sub_C 6
    let mm2 : pm2.Monic := monic_X_sub_C (-2)
    let m2 : p2.Monic := (monic_X_sub_C 2).pow 2
    let m0 : p0.Monic := (monic_X (R := ℂ)).pow 4
    let ms : ps.Monic := (monic_X_sub_C _).pow 4
    let mns : pns.Monic := (monic_X_sub_C _).pow 4
    change (p6 * pm2 * p2 * p0 * ps * pns).natDegree = 16
    rw [((((m6.mul mm2).mul m2).mul m0).mul ms).natDegree_mul mns,
      (((m6.mul mm2).mul m2).mul m0).natDegree_mul ms,
      ((m6.mul mm2).mul m2).natDegree_mul m0,
      (m6.mul mm2).natDegree_mul m2, m6.natDegree_mul mm2]
    simp [p6, pm2, p2, p0, ps, pns]
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    hqmonic B.charpoly_monic hdvd
  rw [Matrix.charpoly_natDegree_eq_dim, hqdeg]
  rw [← Fintype.card_congr e]
  decide

/-- Integer-coefficient form of the same quotient factor. -/
theorem eightEight_centeredCharpoly_eq_integerFactor
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))}) :
    let B := (2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ
    B.charpoly =
      (X - C (6 : ℂ)) * (X - C (-2 : ℂ)) *
        (X - C (2 : ℂ)) ^ 2 * X ^ 4 * (X ^ 2 - C (2 : ℂ)) ^ 4 := by
  dsimp only
  rw [eightEight_centeredCharpoly_eq H e hleft hright]
  let s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
  have hs2 : s ^ 2 = 2 := by
    change (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hquad : (X - C s) * (X - C (-s)) = X ^ 2 - C (2 : ℂ) := by
    rw [show C (-s) = -C s by simp]
    rw [show C (2 : ℂ) = C (s ^ 2) by rw [hs2]]
    rw [map_pow]
    ring
  calc
    (X - C (6 : ℂ)) * (X - C (-2 : ℂ)) *
          (X - C (2 : ℂ)) ^ 2 * X ^ 4 * (X - C s) ^ 4 *
          (X - C (-s)) ^ 4 =
        (X - C (6 : ℂ)) * (X - C (-2 : ℂ)) *
          (X - C (2 : ℂ)) ^ 2 * X ^ 4 *
          ((X - C s) * (X - C (-s))) ^ 4 := by ring
    _ = _ := by rw [hquad]

end

end Erdos85

#print axioms Erdos85.eightEight_centeredCharpoly_candidate_dvd
#print axioms Erdos85.eightEight_centeredCharpoly_eq
#print axioms Erdos85.eightEight_centeredCharpoly_eq_integerFactor
