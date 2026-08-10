import Proofs.Erdos85RationalPrimaryTraceSplit
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Symmetric sector factorization for the uniform trace-split kill

A rational symmetric matrix has a squarefree minimal polynomial at every
linear factor: if `(X - c)² ∣ minpoly`, then the symmetric operator
`aeval A ((X - c)·h)` squares to zero, hence vanishes (a symmetric rational
matrix with zero square is zero, by the sum-of-squares diagonal of its
square), contradicting minimality of the annihilating degree.

Consequently the minimal polynomial of the defect operator splits — after
multiplying in at most one copy of each of the two designated linear
factors — as a product `(X - 2) · (X - μ₀) · r` with the three factors
pairwise coprime.  This is exactly the shape consumed by the three-sector
primary trace split.

The file also provides the transport lemmas used by the residual sector:
restriction to an invariant kernel commutes with polynomial evaluation, a
rational charpoly root over the algebraic closure is realized by a genuine
eigenvector, and a polynomial identity `aeval N r = 0` forces every
eigenvalue of `N` over the closure to be a root of `r`.
-/

open Polynomial
open scoped Matrix

namespace Erdos85

noncomputable section

/-! ## Symmetric matrices and polynomial evaluation -/

/-- Polynomial evaluation commutes with transposition. -/
theorem matrix_transpose_aeval {V : Type*} [Fintype V] [DecidableEq V]
    {K : Type*} [Field K] (A : Matrix V V K) (p : K[X]) :
    (Polynomial.aeval A p)ᵀ = Polynomial.aeval Aᵀ p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Matrix.transpose_add, hp, hq]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Matrix.transpose_mul, Matrix.transpose_pow]
      have h1 : (algebraMap K (Matrix V V K) a)ᵀ =
          algebraMap K (Matrix V V K) a := by
        ext i j
        by_cases h : i = j
        · subst h
          simp [Matrix.algebraMap_matrix_apply]
        · simp [Matrix.algebraMap_matrix_apply, Matrix.transpose_apply, h,
            Ne.symm h]
      rw [h1]
      exact (Algebra.commutes a (Aᵀ ^ n)).symm

/-- Polynomial evaluation preserves symmetry. -/
theorem matrix_isSymm_aeval {V : Type*} [Fintype V] [DecidableEq V]
    {K : Type*} [Field K] {A : Matrix V V K} (hA : A.IsSymm) (p : K[X]) :
    (Polynomial.aeval A p).IsSymm := by
  unfold Matrix.IsSymm
  rw [matrix_transpose_aeval, hA]

/-- A symmetric rational matrix whose square vanishes is zero. -/
theorem matrix_eq_zero_of_isSymm_of_mul_self_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {M : Matrix V V ℚ} (hM : M.IsSymm) (h : M * M = 0) : M = 0 := by
  ext i j
  have hdiag : (∑ l, M i l * M i l) = 0 := by
    have hii := congrFun (congrFun h i) i
    rw [Matrix.mul_apply] at hii
    calc
      (∑ l, M i l * M i l) = ∑ l, M i l * M l i := by
        refine Finset.sum_congr rfl fun l _ => ?_
        have hsymm := congrFun (congrFun hM i) l
        rw [Matrix.transpose_apply] at hsymm
        rw [hsymm]
      _ = 0 := hii
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun l _ => mul_self_nonneg (M i l))).mp hdiag j (Finset.mem_univ j)
  simpa using mul_self_eq_zero.mp hterm

/-- A symmetric rational matrix has no generalized zero vector of height
two: if `M² v = 0`, then already `M v = 0`.  This is the vector form used by
the zero-layer cube-root kernel: the square identity first puts an explicit
Fourier column in `ker M²`, and symmetry lowers it to `ker M`. -/
theorem matrix_mulVec_eq_zero_of_isSymm_of_sq_mulVec_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {M : Matrix V V ℚ} (hM : M.IsSymm) {v : V → ℚ}
    (hzero : (M * M).mulVec v = 0) :
    M.mulVec v = 0 := by
  have hzero' : (Mᵀ * M).mulVec v = 0 := by
    rw [hM]
    exact hzero
  have hv : v ∈ LinearMap.ker (Mᵀ * M).mulVecLin := by
    exact LinearMap.mem_ker.mpr hzero'
  rw [Matrix.ker_mulVecLin_transpose_mul_self M] at hv
  simpa [LinearMap.mem_ker] using hv

/-- **Linear squarefreeness of the symmetric minimal polynomial.**  No
square of a linear factor divides the minimal polynomial of a symmetric
rational matrix. -/
theorem not_X_sub_C_sq_dvd_minpoly_of_isSymm
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℚ} (hA : A.IsSymm) (c : ℚ) :
    ¬ (X - C c) ^ 2 ∣ minpoly ℚ A := by
  intro hdvd
  haveI : Algebra.IsIntegral ℚ (Matrix V V ℚ) :=
    Algebra.IsIntegral.of_finite ℚ _
  have hint : IsIntegral ℚ A := Algebra.IsIntegral.isIntegral A
  have hm0 : minpoly ℚ A ≠ 0 := minpoly.ne_zero hint
  obtain ⟨h, hm⟩ := hdvd
  have hh0 : h ≠ 0 := by
    intro h0
    exact hm0 (by rw [hm, h0, mul_zero])
  have hXc : (X - C c : ℚ[X]) ≠ 0 := X_sub_C_ne_zero c
  -- the symmetric operator `aeval A ((X - c) * h)` squares to zero
  set M : Matrix V V ℚ := Polynomial.aeval A ((X - C c) * h) with hMdef
  have hMsq : M * M = 0 := by
    rw [hMdef, ← map_mul]
    have hpoly : ((X - C c) * h) * ((X - C c) * h) =
        minpoly ℚ A * h := by
      rw [hm]
      ring
    rw [hpoly, map_mul, minpoly.aeval, zero_mul]
  have hMsymm : M.IsSymm := matrix_isSymm_aeval hA _
  have hM0 : M = 0 := matrix_eq_zero_of_isSymm_of_mul_self_eq_zero hMsymm hMsq
  -- so `(X - c) * h` annihilates `A`, contradicting degree minimality
  have hann : Polynomial.aeval A ((X - C c) * h) = 0 := by
    rw [← hMdef, hM0]
  have hprodne : (X - C c) * h ≠ 0 := mul_ne_zero hXc hh0
  have hdvd2 : minpoly ℚ A ∣ (X - C c) * h := minpoly.dvd ℚ A hann
  have hle := Polynomial.natDegree_le_of_dvd hdvd2 hprodne
  have hdeg1 : ((X - C c) * h).natDegree = 1 + h.natDegree := by
    rw [Polynomial.natDegree_mul hXc hh0, Polynomial.natDegree_X_sub_C]
  have hdeg2 : (minpoly ℚ A).natDegree = 2 + h.natDegree := by
    rw [hm, Polynomial.natDegree_mul (pow_ne_zero 2 hXc) hh0,
      Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
  omega

/-- **Sector factorization.**  For a symmetric rational matrix, the minimal
polynomial divides `(X - 2) · (X - μ₀) · r` for some `r` dividing the
minimal polynomial and avoiding the roots `2` and `μ₀`. -/
theorem exists_residual_factor
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℚ} (hA : A.IsSymm) (μ0 : ℚ) :
    ∃ r : ℚ[X], r.eval 2 ≠ 0 ∧ r.eval μ0 ≠ 0 ∧ r ∣ minpoly ℚ A ∧
      minpoly ℚ A ∣ (X - C 2) * (X - C μ0) * r := by
  set m : ℚ[X] := minpoly ℚ A with hmdef
  -- peel one copy of `X - 2` if present
  obtain ⟨m2, hm2dvd, hm2eval, hm2fac⟩ :
      ∃ m2 : ℚ[X], m2 ∣ m ∧ m2.eval 2 ≠ 0 ∧ m ∣ (X - C 2) * m2 := by
    by_cases h2 : (X - C 2 : ℚ[X]) ∣ m
    · obtain ⟨m2, hm2⟩ := h2
      refine ⟨m2, Dvd.intro_left _ hm2.symm, ?_, by rw [hm2]⟩
      intro heval
      have hdvd2 : (X - C 2 : ℚ[X]) ∣ m2 :=
        Polynomial.dvd_iff_isRoot.mpr heval
      obtain ⟨q, hq⟩ := hdvd2
      exact not_X_sub_C_sq_dvd_minpoly_of_isSymm hA 2
        ⟨q, by rw [← hmdef, hm2, hq]; ring⟩
    · refine ⟨m, dvd_rfl, ?_, Dvd.intro_left _ rfl⟩
      intro heval
      exact h2 (Polynomial.dvd_iff_isRoot.mpr heval)
  -- peel one copy of `X - μ0` if present
  by_cases hμ : (X - C μ0 : ℚ[X]) ∣ m2
  · obtain ⟨r, hr⟩ := hμ
    have hrdvd : r ∣ m := dvd_trans (Dvd.intro_left _ hr.symm) hm2dvd
    have hr2 : r.eval 2 ≠ 0 := by
      intro h0
      apply hm2eval
      rw [hr]
      simp [h0]
    have hrμ : r.eval μ0 ≠ 0 := by
      intro h0
      have hdvdr : (X - C μ0 : ℚ[X]) ∣ r := Polynomial.dvd_iff_isRoot.mpr h0
      obtain ⟨q, hq⟩ := hdvdr
      obtain ⟨s, hs⟩ := hm2dvd
      exact not_X_sub_C_sq_dvd_minpoly_of_isSymm hA μ0
        ⟨q * s, by rw [← hmdef, hs, hr, hq]; ring⟩
    refine ⟨r, hr2, hrμ, hrdvd, ?_⟩
    calc
      m ∣ (X - C 2) * m2 := hm2fac
      _ = (X - C 2) * (X - C μ0) * r := by rw [hr]; ring
  · have hrμ : m2.eval μ0 ≠ 0 := by
      intro h0
      exact hμ (Polynomial.dvd_iff_isRoot.mpr h0)
    refine ⟨m2, hm2eval, hrμ, hm2dvd, ?_⟩
    calc
      m ∣ (X - C 2) * m2 := hm2fac
      _ ∣ (X - C 2) * (X - C μ0) * m2 := by
        rw [show (X - C 2 : ℚ[X]) * (X - C μ0) * m2 =
          (X - C μ0) * ((X - C 2) * m2) by ring]
        exact dvd_mul_left _ _

/-! ## Restriction transport -/

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]

/-- Powers of the restriction agree with restricted powers. -/
theorem kerAevalRestrict_pow_coe (S T : E →ₗ[K] E) (hcomm : S * T = T * S)
    (p : K[X]) (n : ℕ) :
    ∀ v : LinearMap.ker (aeval T p),
      (((kerAevalRestrict S T hcomm p) ^ n) v : E) = (S ^ n) (v : E) := by
  induction n with
  | zero => intro v; simp
  | succ n ih =>
      intro v
      rw [pow_succ, pow_succ]
      calc
        (((kerAevalRestrict S T hcomm p ^ n) *
            kerAevalRestrict S T hcomm p) v : E) =
            ((kerAevalRestrict S T hcomm p ^ n)
              ((kerAevalRestrict S T hcomm p) v) : E) := rfl
        _ = (S ^ n) ((kerAevalRestrict S T hcomm p v : E)) :=
          ih ((kerAevalRestrict S T hcomm p) v)
        _ = (S ^ n) (S (v : E)) := by rw [kerAevalRestrict_coe]
        _ = ((S ^ n) * S) (v : E) := rfl

/-- Polynomial evaluation commutes with restriction to the invariant
kernel sector. -/
theorem kerAevalRestrict_aeval_coe (S T : E →ₗ[K] E) (hcomm : S * T = T * S)
    (p : K[X]) (q : K[X]) (v : LinearMap.ker (aeval T p)) :
    ((aeval (kerAevalRestrict S T hcomm p) q) v : E) =
      (aeval S q) (v : E) := by
  induction q using Polynomial.induction_on' with
  | add q₁ q₂ h₁ h₂ =>
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
        Submodule.coe_add, h₁, h₂]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
      have h1 : ((algebraMap K (Module.End K (LinearMap.ker (aeval T p))) a *
          (kerAevalRestrict S T hcomm p) ^ n) v : E) =
          a • (((kerAevalRestrict S T hcomm p) ^ n) v : E) := by
        have : (algebraMap K (Module.End K (LinearMap.ker (aeval T p))) a *
            (kerAevalRestrict S T hcomm p) ^ n) v =
            a • (((kerAevalRestrict S T hcomm p) ^ n) v) := by
          simp [Module.algebraMap_end_apply]
        rw [this, SetLike.val_smul]
      rw [h1, kerAevalRestrict_pow_coe]
      simp [Module.algebraMap_end_apply]

/-- The residual polynomial annihilates the restriction of `T` to its own
kernel sector. -/
theorem aeval_kerAevalRestrict_self (T : E →ₗ[K] E) (r : K[X]) :
    aeval (kerAevalRestrict T T rfl r) r = 0 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [kerAevalRestrict_aeval_coe]
  have hv := v.2
  rw [LinearMap.mem_ker] at hv
  simp [hv]

/-! ## Eigenvector transport over the algebraic closure -/

/-- A rational charpoly root over the algebraic closure is realized by a
genuine eigenvector of the base-changed matrix. -/
theorem matrix_exists_eigenvector_of_aeval_charpoly_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℚ) (θ : AlgebraicClosure ℚ)
    (hθ : Polynomial.aeval θ M.charpoly = 0) :
    ∃ v : ι → AlgebraicClosure ℚ, v ≠ 0 ∧
      (M.map (algebraMap ℚ (AlgebraicClosure ℚ))).mulVec v = θ • v := by
  let ι' : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ)
  have hroot : Polynomial.IsRoot (M.map ι').charpoly θ := by
    change (M.map ι').charpoly.eval θ = 0
    rw [Matrix.charpoly_map]
    simpa [Polynomial.eval_map, Polynomial.aeval_def, ι'] using hθ
  have hspec : θ ∈ spectrum (AlgebraicClosure ℚ) (M.map ι') :=
    Matrix.mem_spectrum_of_isRoot_charpoly hroot
  have heig : Module.End.HasEigenvalue (Matrix.toLin' (M.map ι')) θ :=
    Module.End.HasEigenvalue.of_mem_spectrum (by simpa using hspec)
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  refine ⟨v, hv.2, ?_⟩
  have := hv.apply_eq_smul
  rwa [Matrix.toLin'_apply] at this

/-- A matrix eigenvector evaluates polynomials at the eigenvalue. -/
theorem matrix_aeval_mulVec_of_eigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι (AlgebraicClosure ℚ)) {μ : AlgebraicClosure ℚ}
    {v : ι → AlgebraicClosure ℚ} (hNv : N.mulVec v = μ • v) (p : ℚ[X]) :
    (Polynomial.aeval N p).mulVec v = (Polynomial.aeval μ p) • v := by
  have hpow : ∀ n : ℕ, (N ^ n).mulVec v = (μ ^ n) • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ, ← Matrix.mulVec_mulVec, hNv,
          Matrix.mulVec_smul, ih, smul_smul]
        ring_nf
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, map_add, Matrix.add_mulVec, hp, hq, add_smul]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        ← Matrix.mulVec_mulVec, hpow]
      have halg : (algebraMap ℚ (Matrix ι ι (AlgebraicClosure ℚ)) a) =
          (algebraMap ℚ (AlgebraicClosure ℚ) a) •
            (1 : Matrix ι ι (AlgebraicClosure ℚ)) := by
        rw [Algebra.algebraMap_eq_smul_one, IsScalarTower.algebraMap_smul]
      rw [halg, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul,
        Algebra.smul_def]

/-- If `aeval N r = 0` and `N v = μ • v` with `v ≠ 0`, then `μ` is a root
of `r`. -/
theorem matrix_aeval_eq_zero_of_eigenvector_of_aeval_matrix_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι (AlgebraicClosure ℚ)) {μ : AlgebraicClosure ℚ}
    {v : ι → AlgebraicClosure ℚ} (hv : v ≠ 0)
    (hNv : N.mulVec v = μ • v) {r : ℚ[X]}
    (hr : Polynomial.aeval N r = 0) :
    Polynomial.aeval μ r = 0 := by
  have h := matrix_aeval_mulVec_of_eigenvector N hNv r
  rw [hr] at h
  have hzero : (Polynomial.aeval μ r) • v = 0 := by
    rw [← h]
    simp [Matrix.zero_mulVec]
  rcases smul_eq_zero.mp hzero with h0 | h0
  · exact h0
  · exact absurd h0 hv

end

end Erdos85
