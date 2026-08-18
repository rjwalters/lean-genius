import Proofs.Erdos85InvariantDecomposition
import Proofs.Erdos85EvenCharpolyTrace
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Trace zero for rational square roots of a nonsquare natural

This is the parameter-uniform version of the earlier `X²-6` argument.  A
rational matrix satisfying `M²=cI`, for nonsquare natural `c`, is a module
over the quadratic field `ℚ(√c)`.  Its characteristic polynomial is a power
of `X²-c`, hence is even and the matrix has trace zero.
-/

namespace Erdos85

open Matrix Polynomial

theorem mapsTo_range_of_commute
    {E : Type*} [AddCommGroup E] [Module ℚ E]
    (A P : E →ₗ[ℚ] E) (hcomm : A * P = P * A) :
    ∀ x ∈ LinearMap.range P, A x ∈ LinearMap.range P := by
  rintro _ ⟨y, rfl⟩
  refine ⟨A y, ?_⟩
  have h := LinearMap.congr_fun hcomm y
  simpa only [Module.End.mul_apply] using h.symm

theorem mapsTo_ker_of_commute
    {E : Type*} [AddCommGroup E] [Module ℚ E]
    (A P : E →ₗ[ℚ] E) (hcomm : A * P = P * A) :
    ∀ x ∈ LinearMap.ker P, A x ∈ LinearMap.ker P := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have h := LinearMap.congr_fun hcomm x
  simp only [Module.End.mul_apply, hx, map_zero] at h
  exact h.symm

/-- Trace of an invariant restriction to the range of an idempotent is the
ambient trace of the endomorphism followed by that idempotent. -/
theorem trace_restrict_range_eq_trace_mul_of_idempotent
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (A P : E →ₗ[ℚ] E) (hP : IsIdempotentElem P)
    (hcomm : A * P = P * A) :
    LinearMap.trace ℚ (LinearMap.range P)
        (A.restrict (mapsTo_range_of_commute A P hcomm)) =
      LinearMap.trace ℚ E (A * P) := by
  let U := LinearMap.range P
  let W := LinearMap.ker P
  let hAU := mapsTo_range_of_commute A P hcomm
  have hAPU : ∀ x ∈ U, (A * P) x ∈ U := by
    intro x hx
    exact hAU (P x) ⟨x, rfl⟩
  have hAPW : ∀ x ∈ W, (A * P) x ∈ W := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    simp only [Module.End.mul_apply, hx, map_zero]
  have hsplit := trace_eq_add_trace_restrict_of_isCompl
    (A * P) U W (LinearMap.IsIdempotentElem.isCompl hP) hAPU hAPW
  have hUeq : (A * P).restrict hAPU = A.restrict hAU := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, Module.End.mul_apply]
    obtain ⟨y, hy⟩ := x.property
    have hPx : P x = x := by
      rw [← hy]
      simpa [IsIdempotentElem, Module.End.mul_apply] using
        LinearMap.congr_fun hP y
    rw [hPx]
  have hWeq : (A * P).restrict hAPW = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hx := x.property
    rw [LinearMap.mem_ker] at hx
    simp [LinearMap.restrict_apply, Module.End.mul_apply, hx]
  rw [hUeq, hWeq] at hsplit
  simpa [U, W] using hsplit.symm

noncomputable def quadraticNat (c : ℕ) : ℚ[X] :=
  X ^ 2 - Polynomial.C (c : ℚ)

theorem quadraticNat_monic (c : ℕ) : (quadraticNat c).Monic := by
  apply (monic_X_pow 2).sub_of_left
  exact degree_C_le.trans_lt (by norm_num)

theorem quadraticNat_natDegree (c : ℕ) : (quadraticNat c).natDegree = 2 := by
  change (X ^ 2 - Polynomial.C (c : ℚ)).natDegree = 2
  compute_degree <;> norm_num

theorem quadraticNat_irreducible {c : ℕ} (hc : ¬ IsSquare c) :
    Irreducible (quadraticNat c) := by
  have hnonsquare : ¬ IsSquare (c : ℚ) := by
    rw [Rat.isSquare_natCast_iff]
    exact hc
  rw [(quadraticNat_monic c).irreducible_iff_roots_eq_zero_of_degree_le_three]
  · rw [Multiset.eq_zero_iff_forall_notMem]
    intro x hx
    have hpne : quadraticNat c ≠ 0 := (quadraticNat_monic c).ne_zero
    have hroot : x ^ 2 = (c : ℚ) := by
      have heval := (mem_roots hpne).mp hx
      rw [IsRoot.def] at heval
      simp [quadraticNat] at heval
      linarith
    apply hnonsquare
    exact ⟨x, by simpa [pow_two] using hroot.symm⟩
  · rw [quadraticNat_natDegree]
  · rw [quadraticNat_natDegree]
    norm_num

theorem charpoly_dvd_quadraticNat_pow
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℚ) (c : ℕ)
    (hM : M * M = (c : ℚ) • (1 : Matrix I I ℚ)) :
    M.charpoly ∣ quadraticNat c ^ Fintype.card I := by
  let N : Matrix I I ℚ[X] :=
    Matrix.scalar I X + M.map (Polynomial.C : ℚ →+* ℚ[X])
  refine ⟨Matrix.det N, ?_⟩
  rw [Matrix.charpoly, ← Matrix.det_mul]
  have hprod : M.charmatrix * N = Matrix.scalar I (quadraticNat c) := by
    let S : Matrix I I ℚ[X] := Matrix.scalar I X
    let Cq : Matrix I I ℚ[X] := M.map (Polynomial.C : ℚ →+* ℚ[X])
    have hS : S = (X : ℚ[X]) • (1 : Matrix I I ℚ[X]) := by
      apply Matrix.ext
      intro i j
      simp [S, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
    have hcomm : S * Cq = Cq * S := by
      rw [hS, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    have hCq2 : Cq * Cq = (c : ℚ[X]) • (1 : Matrix I I ℚ[X]) := by
      change M.map (Polynomial.C : ℚ →+* ℚ[X]) *
          M.map (Polynomial.C : ℚ →+* ℚ[X]) = _
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
    change (S - Cq) * (S + Cq) = Matrix.scalar I (quadraticNat c)
    calc
      (S - Cq) * (S + Cq) = S * S - Cq * Cq := by
        rw [sub_mul, mul_add, mul_add, hcomm]
        abel
      _ = Matrix.scalar I (X ^ 2) -
          (c : ℚ[X]) • (1 : Matrix I I ℚ[X]) := by rw [hS2, hCq2]
      _ = Matrix.scalar I (quadraticNat c) := by
        apply Matrix.ext
        intro i j
        simp [quadraticNat, Matrix.diagonal_apply,
          Matrix.smul_apply, Matrix.one_apply]
        split_ifs <;> simp
  rw [hprod]
  simpa [Matrix.scalar, Matrix.det_diagonal]

/-- A rational matrix whose square is a nonsquare natural scalar has trace
zero.  Evenness of the dimension is a consequence, not a hypothesis. -/
theorem Matrix.trace_eq_zero_of_sq_eq_nonsquare_nat
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (M : Matrix I I ℚ) (c : ℕ) (hc : ¬ IsSquare c)
    (hM : M * M = (c : ℚ) • (1 : Matrix I I ℚ)) :
    Matrix.trace M = 0 := by
  have hdvd := charpoly_dvd_quadraticNat_pow M c hM
  obtain ⟨k, hk, hassoc⟩ :=
    (dvd_prime_pow (quadraticNat_irreducible hc).prime
      (Fintype.card I)).mp hdvd
  have hchar : M.charpoly = quadraticNat c ^ k :=
    Polynomial.eq_of_monic_of_associated M.charpoly_monic
      ((quadraticNat_monic c).pow k) hassoc
  have hdeg := congrArg Polynomial.natDegree hchar
  rw [Matrix.charpoly_natDegree_eq_dim,
    (quadraticNat_monic c).natDegree_pow, quadraticNat_natDegree] at hdeg
  have hcard : Fintype.card I = 2 * k := by omega
  have hquad : quadraticNat c =
      Polynomial.expand ℚ 2 (X - Polynomial.C (c : ℚ)) := by
    change X ^ 2 - Polynomial.C (c : ℚ) =
      Polynomial.expand ℚ 2 (X - Polynomial.C (c : ℚ))
    rw [map_sub, Polynomial.expand_X, Polynomial.expand_C]
  have hcharExpand : M.charpoly =
      Polynomial.expand ℚ 2 ((X - Polynomial.C (c : ℚ)) ^ k) := by
    rw [hchar, hquad, map_pow]
  apply Matrix.trace_eq_zero_of_charpoly_eq_expand_two
    M ((X - Polynomial.C (c : ℚ)) ^ k) hcharExpand
  exact ⟨k, by omega⟩

/-- Endomorphism form of the parameter-uniform quadratic trace theorem. -/
theorem LinearMap.trace_eq_zero_of_sq_eq_nonsquare_nat
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    [Nontrivial E]
    (T : E →ₗ[ℚ] E) (c : ℕ) (hc : ¬ IsSquare c)
    (hT : T * T = (c : ℚ) • LinearMap.id) :
    LinearMap.trace ℚ E T = 0 := by
  let b := Module.Free.chooseBasis ℚ E
  let M := LinearMap.toMatrix b b T
  letI : Nonempty (Module.Free.ChooseBasisIndex ℚ E) :=
    Fintype.card_pos_iff.mp (by
      rw [← Module.finrank_eq_card_chooseBasisIndex]
      exact Module.finrank_pos)
  have hM : M * M =
      (c : ℚ) • (1 : Matrix (Module.Free.ChooseBasisIndex ℚ E)
        (Module.Free.ChooseBasisIndex ℚ E) ℚ) := by
    have hmapped := congrArg (LinearMap.toMatrix b b) hT
    simpa [M, LinearMap.toMatrix_mul, LinearMap.toMatrix_id] using hmapped
  rw [LinearMap.trace_eq_matrix_trace ℚ b]
  exact Matrix.trace_eq_zero_of_sq_eq_nonsquare_nat M c hc hM

/-- Abstract complementary-space trace contradiction used by quotient
projections. -/
theorem false_of_complementary_traces_sq_nonsquare_nat
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (A : E →ₗ[ℚ] E) (U W : Submodule ℚ E) [Nontrivial W]
    (hcompl : IsCompl U W)
    (hU : ∀ x ∈ U, A x ∈ U) (hW : ∀ x ∈ W, A x ∈ W)
    (htrace : LinearMap.trace ℚ E A = 0)
    (q : ℚ) (hq : q ≠ 0)
    (hUtrace : LinearMap.trace ℚ U (A.restrict hU) = q)
    (c : ℕ) (hc : ¬ IsSquare c)
    (hWsq : (A.restrict hW) * (A.restrict hW) =
      (c : ℚ) • LinearMap.id) : False := by
  have hsplit := trace_eq_add_trace_restrict_of_isCompl
    A U W hcompl hU hW
  have hzero : LinearMap.trace ℚ W (A.restrict hW) = 0 :=
    LinearMap.trace_eq_zero_of_sq_eq_nonsquare_nat
      (A.restrict hW) c hc hWsq
  rw [htrace, hUtrace, hzero, add_zero] at hsplit
  exact hq hsplit.symm

/-- Positive trace on one summand and zero total trace force the scalar on the
complementary quadratic summand to be a square. -/
theorem isSquare_of_complementary_traces_sq_nat
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (A : E →ₗ[ℚ] E) (U W : Submodule ℚ E) [Nontrivial W]
    (hcompl : IsCompl U W)
    (hU : ∀ x ∈ U, A x ∈ U) (hW : ∀ x ∈ W, A x ∈ W)
    (htrace : LinearMap.trace ℚ E A = 0)
    (q : ℚ) (hq : q ≠ 0)
    (hUtrace : LinearMap.trace ℚ U (A.restrict hU) = q)
    (c : ℕ)
    (hWsq : (A.restrict hW) * (A.restrict hW) =
      (c : ℚ) • LinearMap.id) : IsSquare c := by
  by_contra hc
  exact false_of_complementary_traces_sq_nonsquare_nat
    A U W hcompl hU hW htrace q hq hUtrace c hc hWsq

/-- If a rational endomorphism squares to the square of a positive integer,
then its trace is an integral multiple of that integer.  Indeed,
`(I + T/t)/2` is an idempotent, so its trace is the dimension of its range.
This packages the usual `+t`/`-t` eigenspace multiplicity argument without
choosing eigenbases. -/
theorem LinearMap.exists_int_mul_eq_trace_of_sq_eq_square_nat
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (T : E →ₗ[ℚ] E) (t : ℕ) (ht : 0 < t)
    (hT : T * T = ((t * t : ℕ) : ℚ) • LinearMap.id) :
    ∃ z : ℤ, LinearMap.trace ℚ E T = (z : ℚ) * t := by
  let S : E →ₗ[ℚ] E := (t : ℚ)⁻¹ • T
  let P : E →ₗ[ℚ] E := (2 : ℚ)⁻¹ • (LinearMap.id + S)
  have htq : (t : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have hS : S * S = LinearMap.id := by
    ext x
    have hx := LinearMap.congr_fun hT x
    change (t : ℚ)⁻¹ • T ((t : ℚ)⁻¹ • T x) = x
    rw [map_smul, smul_smul]
    change ((t : ℚ)⁻¹ * (t : ℚ)⁻¹) • (T * T) x = x
    rw [hx]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    change (((t : ℚ)⁻¹ * (t : ℚ)⁻¹) * (t * t : ℕ)) • x = x
    have hc : (t : ℚ)⁻¹ * (t : ℚ)⁻¹ * (t * t : ℕ) = 1 := by
      push_cast
      field_simp
    rw [hc, one_smul]
  have hP : IsIdempotentElem P := by
    rw [IsIdempotentElem]
    ext x
    have hsx : S (S x) = x := by
      simpa only [Module.End.mul_apply, LinearMap.id_coe, id_eq] using
        LinearMap.congr_fun hS x
    change (2 : ℚ)⁻¹ • ((2 : ℚ)⁻¹ • (x + S x) +
      S ((2 : ℚ)⁻¹ • (x + S x))) = (2 : ℚ)⁻¹ • (x + S x)
    rw [map_smul, map_add, hsx]
    module
  have hproj := LinearMap.IsIdempotentElem.isProj_range P hP
  have htraceP := hproj.trace
  have htrace_expand : LinearMap.trace ℚ E P =
      (2 : ℚ)⁻¹ * ((Module.finrank ℚ E : ℚ) +
        (t : ℚ)⁻¹ * LinearMap.trace ℚ E T) := by
    simp only [P, S, map_smul, map_add, LinearMap.trace_id]
    ring
  rw [htrace_expand] at htraceP
  let r : ℕ := Module.finrank ℚ (LinearMap.range P)
  refine ⟨(2 * (r : ℤ) - (Module.finrank ℚ E : ℤ)), ?_⟩
  have hr : (r : ℚ) =
      (2 : ℚ)⁻¹ * ((Module.finrank ℚ E : ℚ) +
        (t : ℚ)⁻¹ * LinearMap.trace ℚ E T) := by
    simpa [r] using htraceP.symm
  push_cast
  field_simp at hr ⊢
  linarith

end Erdos85
