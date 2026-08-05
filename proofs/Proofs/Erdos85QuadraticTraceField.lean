import Proofs.Erdos85QuadraticTrace

/-!
# Trace zero for a nonsquare scalar over an arbitrary field

This is the field-valued form needed by the Fourier eigenspaces.  If an
endomorphism satisfies `T² = λ I` and `λ` is not a square in the ground
field, then its characteristic polynomial is a power of `X² - λ`; in
particular it is even, so its trace vanishes.
-/

namespace Erdos85

open Matrix Polynomial

noncomputable def quadraticScalar {K : Type*} [Field K] (a : K) : K[X] :=
  X ^ 2 - Polynomial.C a

theorem quadraticScalar_monic {K : Type*} [Field K] (a : K) :
    (quadraticScalar a).Monic := by
  apply (monic_X_pow 2).sub_of_left
  exact degree_C_le.trans_lt (by norm_num)

theorem quadraticScalar_natDegree {K : Type*} [Field K] (a : K) :
    (quadraticScalar a).natDegree = 2 := by
  change (X ^ 2 - Polynomial.C a).natDegree = 2
  compute_degree <;> norm_num

theorem quadraticScalar_irreducible {K : Type*} [Field K] {a : K}
    (ha : ¬ IsSquare a) : Irreducible (quadraticScalar a) := by
  rw [(quadraticScalar_monic a).irreducible_iff_roots_eq_zero_of_degree_le_three]
  · rw [Multiset.eq_zero_iff_forall_notMem]
    intro x hx
    have hpne : quadraticScalar a ≠ 0 := (quadraticScalar_monic a).ne_zero
    have hroot : x ^ 2 = a := by
      have heval := (mem_roots hpne).mp hx
      rw [IsRoot.def] at heval
      simp [quadraticScalar] at heval
      exact sub_eq_zero.mp heval
    exact ha ⟨x, by simpa [pow_two] using hroot.symm⟩
  · rw [quadraticScalar_natDegree]
  · rw [quadraticScalar_natDegree]
    norm_num

theorem charpoly_dvd_quadraticScalar_pow
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (M : Matrix I I K) (a : K)
    (hM : M * M = a • (1 : Matrix I I K)) :
    M.charpoly ∣ quadraticScalar a ^ Fintype.card I := by
  let N : Matrix I I K[X] :=
    Matrix.scalar I X + M.map (Polynomial.C : K →+* K[X])
  refine ⟨Matrix.det N, ?_⟩
  rw [Matrix.charpoly, ← Matrix.det_mul]
  have hprod : M.charmatrix * N = Matrix.scalar I (quadraticScalar a) := by
    let S : Matrix I I K[X] := Matrix.scalar I X
    let Cq : Matrix I I K[X] := M.map (Polynomial.C : K →+* K[X])
    have hS : S = (X : K[X]) • (1 : Matrix I I K[X]) := by
      apply Matrix.ext
      intro i j
      simp [S, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
    have hcomm : S * Cq = Cq * S := by
      rw [hS, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    have hCq2 : Cq * Cq = Polynomial.C a • (1 : Matrix I I K[X]) := by
      change M.map (Polynomial.C : K →+* K[X]) *
          M.map (Polynomial.C : K →+* K[X]) = _
      rw [← Matrix.map_mul, hM]
      apply Matrix.ext
      intro i j
      simp [Matrix.smul_apply, Matrix.one_apply]
      split_ifs <;> simp
    have hS2 : S * S = Matrix.scalar I (X ^ 2) := by
      rw [hS, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
      apply Matrix.ext
      intro i j
      simp [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, pow_two]
    change (S - Cq) * (S + Cq) = Matrix.scalar I (quadraticScalar a)
    calc
      (S - Cq) * (S + Cq) = S * S - Cq * Cq := by
        rw [sub_mul, mul_add, mul_add, hcomm]
        abel
      _ = Matrix.scalar I (X ^ 2) -
          Polynomial.C a • (1 : Matrix I I K[X]) := by rw [hS2, hCq2]
      _ = Matrix.scalar I (quadraticScalar a) := by
        apply Matrix.ext
        intro i j
        simp [quadraticScalar, Matrix.diagonal_apply,
          Matrix.smul_apply, Matrix.one_apply]
        split_ifs <;> simp
  rw [hprod]
  simpa [Matrix.scalar, Matrix.det_diagonal]

/-- A matrix whose square is a nonsquare scalar has trace zero. -/
theorem Matrix.trace_eq_zero_of_sq_eq_nonsquare
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I] [Nonempty I]
    (M : Matrix I I K) (a : K) (ha : ¬ IsSquare a)
    (hM : M * M = a • (1 : Matrix I I K)) : Matrix.trace M = 0 := by
  have hdvd := charpoly_dvd_quadraticScalar_pow M a hM
  obtain ⟨k, hk, hassoc⟩ :=
    (dvd_prime_pow (quadraticScalar_irreducible ha).prime
      (Fintype.card I)).mp hdvd
  have hchar : M.charpoly = quadraticScalar a ^ k :=
    Polynomial.eq_of_monic_of_associated M.charpoly_monic
      ((quadraticScalar_monic a).pow k) hassoc
  have hdeg := congrArg Polynomial.natDegree hchar
  rw [Matrix.charpoly_natDegree_eq_dim,
    (quadraticScalar_monic a).natDegree_pow, quadraticScalar_natDegree] at hdeg
  have hcard : Fintype.card I = 2 * k := by omega
  have hquad : quadraticScalar a =
      Polynomial.expand K 2 (X - Polynomial.C a) := by
    change X ^ 2 - Polynomial.C a =
      Polynomial.expand K 2 (X - Polynomial.C a)
    rw [map_sub, Polynomial.expand_X, Polynomial.expand_C]
  have hcharExpand : M.charpoly =
      Polynomial.expand K 2 ((X - Polynomial.C a) ^ k) := by
    rw [hchar, hquad, map_pow]
  rw [Matrix.trace_eq_neg_charpoly_coeff, hcharExpand,
    Polynomial.coeff_expand (by norm_num : 0 < 2)]
  have hodd : ¬ 2 ∣ Fintype.card I - 1 := by
    intro hdvd
    obtain ⟨j, hj⟩ := hdvd
    have hcardpos : 0 < Fintype.card I := Fintype.card_pos
    omega
  simp [hodd]

/-- Endomorphism form of the field-valued nonsquare trace theorem. -/
theorem LinearMap.trace_eq_zero_of_sq_eq_nonsquare
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] [Nontrivial E]
    (T : E →ₗ[K] E) (a : K) (ha : ¬ IsSquare a)
    (hT : T * T = a • LinearMap.id) : LinearMap.trace K E T = 0 := by
  let b := Module.Free.chooseBasis K E
  let M := LinearMap.toMatrix b b T
  letI : Nonempty (Module.Free.ChooseBasisIndex K E) :=
    Fintype.card_pos_iff.mp (by
      rw [← Module.finrank_eq_card_chooseBasisIndex]
      exact Module.finrank_pos)
  have hM : M * M =
      a • (1 : Matrix (Module.Free.ChooseBasisIndex K E)
        (Module.Free.ChooseBasisIndex K E) K) := by
    have hmapped := congrArg (LinearMap.toMatrix b b) hT
    simpa [M, LinearMap.toMatrix_mul, LinearMap.toMatrix_id] using hmapped
  rw [LinearMap.trace_eq_matrix_trace K b]
  exact Matrix.trace_eq_zero_of_sq_eq_nonsquare M a ha hM

end Erdos85
