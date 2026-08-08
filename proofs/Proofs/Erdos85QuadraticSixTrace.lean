import Proofs.Erdos85EvenCharpolyTrace
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Trace zero for rational square roots of six

The degree-six triangle complement carries an endomorphism `T` satisfying
`T² = 6I`.  Since `X²-6` is irreducible over `ℚ`, its characteristic
polynomial is a power of that quadratic and therefore has zero trace.
-/

namespace Erdos85

open Matrix Polynomial

noncomputable def quadraticSix : ℚ[X] := X ^ 2 - 6

theorem quadraticSix_monic : quadraticSix.Monic := by
  apply (monic_X_pow 2).sub_of_left
  exact degree_C_le.trans_lt (by norm_num)

theorem quadraticSix_natDegree : quadraticSix.natDegree = 2 := by
  change (X ^ 2 - (6 : ℚ[X])).natDegree = 2
  compute_degree <;> norm_num

theorem quadraticSix_irreducible : Irreducible quadraticSix := by
  have hnonsquare : ¬ IsSquare (6 : ℚ) := by
    have hn : ¬ IsSquare ((6 : ℕ) : ℚ) := by
      rw [Rat.isSquare_natCast_iff]
      rintro ⟨a, ha⟩
      have hdiv : a ∣ 6 := ⟨a, ha⟩
      have hle : a ≤ 6 := Nat.le_of_dvd (by norm_num) hdiv
      interval_cases a <;> omega
    exact hn
  rw [quadraticSix_monic.irreducible_iff_roots_eq_zero_of_degree_le_three]
  · rw [Multiset.eq_zero_iff_forall_notMem]
    intro x hx
    have hpne : quadraticSix ≠ 0 := quadraticSix_monic.ne_zero
    have hroot : x ^ 2 = (6 : ℚ) := by
      have heval := (mem_roots hpne).mp hx
      rw [IsRoot.def] at heval
      simp [quadraticSix] at heval
      linarith
    apply hnonsquare
    exact ⟨x, by simpa [pow_two] using hroot.symm⟩
  · rw [quadraticSix_natDegree]
  · rw [quadraticSix_natDegree]
    norm_num

/-- The characteristic polynomial of a rational matrix whose square is six
times the identity divides the corresponding power of `X²-6`. -/
theorem charpoly_dvd_quadraticSix_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ)
    (hM : M * M = (6 : ℚ) • (1 : Matrix ι ι ℚ)) :
    M.charpoly ∣ quadraticSix ^ Fintype.card ι := by
  let N : Matrix ι ι ℚ[X] :=
    Matrix.scalar ι X + M.map (Polynomial.C : ℚ →+* ℚ[X])
  refine ⟨Matrix.det N, ?_⟩
  rw [Matrix.charpoly, ← Matrix.det_mul]
  have hprod : M.charmatrix * N = Matrix.scalar ι quadraticSix := by
    let S : Matrix ι ι ℚ[X] := Matrix.scalar ι X
    let Cq : Matrix ι ι ℚ[X] := M.map (Polynomial.C : ℚ →+* ℚ[X])
    have hS : S = (X : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) := by
      apply Matrix.ext
      intro i j
      simp [S, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
    have hcomm : S * Cq = Cq * S := by
      rw [hS, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    have hCq2 : Cq * Cq = (6 : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) := by
      change M.map (Polynomial.C : ℚ →+* ℚ[X]) *
          M.map (Polynomial.C : ℚ →+* ℚ[X]) = _
      rw [← Matrix.map_mul, hM]
      apply Matrix.ext
      intro i j
      simp [Matrix.smul_apply, Matrix.one_apply]
      split_ifs
      · change Polynomial.C (6 : ℚ) = Polynomial.C (6 : ℚ)
        rfl
      · simp
    have hS2 : S * S = Matrix.scalar ι (X ^ 2) := by
      rw [hS, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
      apply Matrix.ext
      intro i j
      simp [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, pow_two]
    change (S - Cq) * (S + Cq) = Matrix.scalar ι quadraticSix
    calc
      (S - Cq) * (S + Cq) = S * S - Cq * Cq := by
        rw [sub_mul, mul_add, mul_add, hcomm]
        abel
      _ = Matrix.scalar ι (X ^ 2) -
          (6 : ℚ[X]) • (1 : Matrix ι ι ℚ[X]) := by rw [hS2, hCq2]
      _ = Matrix.scalar ι quadraticSix := by
        apply Matrix.ext
        intro i j
        simp [quadraticSix, Matrix.diagonal_apply,
          Matrix.smul_apply, Matrix.one_apply]
        split_ifs <;> simp
  rw [hprod]
  simpa [Matrix.scalar, Matrix.det_diagonal]

/-- In dimension 22 the only possible characteristic polynomial is the
eleventh power of `X²-6`. -/
theorem charpoly_eq_quadraticSix_pow_eleven
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ)
    (hcard : Fintype.card ι = 22)
    (hM : M * M = (6 : ℚ) • (1 : Matrix ι ι ℚ)) :
    M.charpoly = quadraticSix ^ 11 := by
  have hdvd := charpoly_dvd_quadraticSix_pow M hM
  rw [hcard] at hdvd
  obtain ⟨k, hk, hassoc⟩ :=
    (dvd_prime_pow quadraticSix_irreducible.prime 22).mp hdvd
  have heq : M.charpoly = quadraticSix ^ k :=
    Polynomial.eq_of_monic_of_associated M.charpoly_monic
      (quadraticSix_monic.pow k) hassoc
  have hdeg := congrArg Polynomial.natDegree heq
  rw [Matrix.charpoly_natDegree_eq_dim,
    quadraticSix_monic.natDegree_pow, quadraticSix_natDegree, hcard] at hdeg
  have hk11 : k = 11 := by omega
  simpa [hk11] using heq

/-- A 22-dimensional rational matrix whose square is six times the identity
has trace zero. -/
theorem Matrix.trace_eq_zero_of_sq_eq_six_of_card_twentyTwo
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℚ)
    (hcard : Fintype.card ι = 22)
    (hM : M * M = (6 : ℚ) • (1 : Matrix ι ι ℚ)) :
    Matrix.trace M = 0 := by
  have hchar := charpoly_eq_quadraticSix_pow_eleven M hcard hM
  have hquad : quadraticSix =
      Polynomial.expand ℚ 2 (X - Polynomial.C (6 : ℚ)) := by
    change X ^ 2 - Polynomial.C (6 : ℚ) =
      Polynomial.expand ℚ 2 (X - Polynomial.C (6 : ℚ))
    rw [map_sub, Polynomial.expand_X, Polynomial.expand_C]
  have hcharExpand : M.charpoly =
      Polynomial.expand ℚ 2 ((X - Polynomial.C (6 : ℚ)) ^ 11) := by
    rw [hchar, hquad, map_pow]
  apply Matrix.trace_eq_zero_of_charpoly_eq_expand_two
    M ((X - Polynomial.C (6 : ℚ)) ^ 11) hcharExpand
    (by rw [hcard]; exact even_iff_two_dvd.mpr (by norm_num))

/-- Endomorphism form used by the triangle-projection complement. -/
theorem LinearMap.trace_eq_zero_of_sq_eq_six_of_finrank_twentyTwo
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (T : E →ₗ[ℚ] E)
    (hfinrank : Module.finrank ℚ E = 22)
    (hT : T * T = (6 : ℚ) • LinearMap.id) :
    LinearMap.trace ℚ E T = 0 := by
  let b := Module.Free.chooseBasis ℚ E
  let M := LinearMap.toMatrix b b T
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℚ E) = 22 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex ℚ E]
    exact hfinrank
  letI : Nonempty (Module.Free.ChooseBasisIndex ℚ E) :=
    Fintype.card_pos_iff.mp (by rw [hcard]; norm_num)
  have hM : M * M =
      (6 : ℚ) • (1 : Matrix (Module.Free.ChooseBasisIndex ℚ E)
        (Module.Free.ChooseBasisIndex ℚ E) ℚ) := by
    have hmapped := congrArg (LinearMap.toMatrix b b) hT
    simpa [M, LinearMap.toMatrix_mul, LinearMap.toMatrix_id] using hmapped
  rw [LinearMap.trace_eq_matrix_trace ℚ b]
  exact Matrix.trace_eq_zero_of_sq_eq_six_of_card_twentyTwo M hcard hM

end Erdos85
