import Mathlib
import Proofs.CayleyHamiltonOQ01
import Proofs.CayleyHamiltonReductionOQ02OQ01

/-
# Matrix Exponential as Polynomial in M via Minimal Polynomial Reduction

## Problem Statement

For any n×n real matrix M and t : ℝ, the matrix exponential exp(t·M) equals
a polynomial in M of degree strictly less than d = deg(minpoly ℝ M):

    exp(t·M) = ∑_{k=0}^{d-1}  p_k(t) · M^k

where  p_k(t) = ∑_{m≥0} (t^m/m!) · coeff_k(X^m mod μ_M).

## Mathematical Proof Chain

1. **Series**: exp(t·M) = ∑_{m≥0} t^m/m! · M^m  (NormedSpace.exp_eq_tsum)
2. **Basis**: M^m = ∑_{k<d} c_{m,k} · M^k  (CayleyHamiltonOQ01 + eval₂_eq_sum_range')
3. **Entry-wise interchange**: work at each matrix entry (i,j):
   ∑_m f_m · ∑_k c_{m,k} · v_k = ∑_k (∑_m f_m · c_{m,k}) · v_k (tsum_sum in ℝ)
4. **Identification**: p_k(t) = ∑_{m≥0} t^m/m! · c_{m,k}

## Key Summability Proof

`expPolyCoeff_summable` is proved (without axioms) via the companion matrix C of μ_M:
  - c_{m,k} = (C^m)_{k,0} (KEY IDENTITY, proved via aeval + orbit structure)
  - |c_{m,k}| ≤ ‖C^m‖ ≤ ‖C‖^m (matrix norm bound)
  - ∑_m |t|^m ‖C‖^m/m! = exp(|t|‖C‖) < ∞ (summable by comparison with exp series)
-/

open Matrix Polynomial BigOperators NormedSpace Finset

namespace CayleyHamiltonOQ01OQ03

variable {n : Type*} [DecidableEq n] [Fintype n] [Nontrivial (Matrix n n ℝ)]
variable (M : Matrix n n ℝ)

-- ============================================================
-- Helper lemmas (needed throughout)
-- ============================================================

private lemma minpoly_natDegree_pos : 0 < (minpoly ℝ M).natDegree :=
  CayleyHamiltonOQ01.minpoly_degree_pos M

private lemma modByMonic_natDegree_lt (m : ℕ) :
    ((X : ℝ[X]) ^ m %ₘ minpoly ℝ M).natDegree < (minpoly ℝ M).natDegree := by
  rcases eq_or_ne ((X : ℝ[X]) ^ m %ₘ minpoly ℝ M) 0 with h | h
  · simp only [h, Polynomial.natDegree_zero]; exact minpoly_natDegree_pos M
  · exact CayleyHamiltonOQ01.degree_mod_minpoly_lt M (X ^ m) h

-- ============================================================
-- Section 1: The Coefficient Functions p_k(t)
-- ============================================================

/-- For k < d = deg(μ_M), the k-th coefficient polynomial:
    p_k(t) = ∑_{m≥0} (t^m/m!) · coeff_k(X^m mod μ_M). -/
noncomputable def expPolyCoeff (k : ℕ) (t : ℝ) : ℝ :=
  ∑' m : ℕ, (t ^ m / (m.factorial : ℝ)) * ((X : ℝ[X]) ^ m %ₘ minpoly ℝ M).coeff k

-- ============================================================
-- Section 1b: Summability Proof via Companion Matrix
-- ============================================================

-- KEY IDENTITY: coeff k (X^m %ₘ μ) = (companionMatrix μ)^m ⟨k,hk⟩ ⟨0,hd⟩
-- Proof: The companion matrix C of μ satisfies minpoly ℝ C = μ, so
--   C^m = aeval C (X^m) = aeval C (X^m %ₘ μ) = ∑_{j<d} c_{m,j} C^j
-- Taking entry (k,0) and using (C^j)_{k,0} = δ_{k,j} (from companionMatrix_pow_basis):
--   C^m ⟨k,hk⟩ ⟨0,hd⟩ = ∑_{j<d} c_{m,j} * δ_{k,j} = c_{m,k} ✓
private lemma coeff_pow_X_eq_companion (m k : ℕ) (hk : k < (minpoly ℝ M).natDegree) :
    ((X : ℝ[X]) ^ m %ₘ minpoly ℝ M).coeff k =
    (CayleyHamiltonReductionOQ02OQ01.companionMatrix (d := (minpoly ℝ M).natDegree)
      (minpoly ℝ M)) ^ m ⟨k, hk⟩ ⟨0, minpoly_natDegree_pos M⟩ := by
  set μ := minpoly ℝ M
  set d := μ.natDegree
  have hd : 0 < d := minpoly_natDegree_pos M
  have hμ_monic : μ.Monic := minpoly.monic (Matrix.isIntegral M)
  set C := CayleyHamiltonReductionOQ02OQ01.companionMatrix (d := d) μ
  -- Establish [NeZero d] for minpoly_companionMatrix
  haveI : NeZero d := ⟨by omega⟩
  -- The companion matrix satisfies minpoly ℝ C = μ
  have hminpoly_C : minpoly ℝ C = μ :=
    CayleyHamiltonReductionOQ02OQ01.minpoly_companionMatrix hμ_monic rfl
  -- C^m = aeval C (X^m) = aeval C (X^m %ₘ μ)  [since minpoly C = μ]
  have hC_aeval : C ^ m = aeval C ((X : ℝ[X]) ^ m %ₘ μ) := by
    have heq := CayleyHamiltonOQ01.aeval_eq_aeval_mod_minpoly C ((X : ℝ[X]) ^ m)
    rwa [hminpoly_C, map_pow, aeval_X] at heq
  -- Basis expansion: aeval C (X^m %ₘ μ) = ∑_{j<d} c_{m,j} · C^j
  have hbasis : C ^ m = ∑ j ∈ Finset.range d,
      ((X : ℝ[X]) ^ m %ₘ μ).coeff j • C ^ j := by
    rw [hC_aeval, aeval_def, eval₂_eq_sum_range' (modByMonic_natDegree_lt M m)]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  -- Take entry (k, 0): C^m ⟨k,hk⟩ ⟨0,hd⟩ = ∑_{j<d} c_{m,j} * C^j ⟨k,hk⟩ ⟨0,hd⟩
  have h_entry : C ^ m ⟨k, hk⟩ ⟨0, hd⟩ =
      ∑ j ∈ Finset.range d,
        ((X : ℝ[X]) ^ m %ₘ μ).coeff j * C ^ j ⟨k, hk⟩ ⟨0, hd⟩ := by
    have := congr_arg (· ⟨k, hk⟩ ⟨0, hd⟩) hbasis
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at this
    exact this
  -- Entry formula: C^j ⟨k,hk⟩ ⟨0,hd⟩ = δ_{j,k}  [companionMatrix_pow_basis]
  -- Using Pi.single i a applied at ⟨k,hk⟩ gives if i = ⟨k,hk⟩ then a else 0
  have hC_pow_entry : ∀ j : ℕ, ∀ hj : j < d,
      C ^ j ⟨k, hk⟩ ⟨0, hd⟩ = if j = k then 1 else 0 := by
    intro j hj
    have horbit := CayleyHamiltonReductionOQ02OQ01.companionMatrix_pow_basis μ j hj
    have h2 := congr_fun horbit ⟨k, hk⟩
    simp only [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
               Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.mk.injEq] at h2
    exact h2
  -- Collapse the sum using sum_eq_single
  rw [h_entry, Finset.sum_eq_single k]
  · rw [hC_pow_entry k hk, if_pos rfl, mul_one]
  · intro j hj hjk
    rw [hC_pow_entry j (Finset.mem_range.mp hj), if_neg hjk, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr hk) h

/-- The series defining p_k(t) converges.
    Proof: coeff_k(X^m mod μ) = (C^m)_{k,0} where C is the companion matrix of μ_M.
    Since |c_{m,k}| ≤ ‖C‖^m (matrix norm bound), the comparison test gives convergence:
    ∑_m |t^m/m!| · |c_{m,k}| ≤ ∑_m (|t|‖C‖)^m/m! = exp(|t|‖C‖) < ∞. -/
theorem expPolyCoeff_summable (k : ℕ) (t : ℝ) :
    Summable (fun m : ℕ =>
      (t ^ m / (m.factorial : ℝ)) * ((X : ℝ[X]) ^ m %ₘ minpoly ℝ M).coeff k) := by
  by_cases hk : k < (minpoly ℝ M).natDegree
  · -- Case k < d: use companion matrix identity + norm bound
    have hd : 0 < (minpoly ℝ M).natDegree := minpoly_natDegree_pos M
    set C := CayleyHamiltonReductionOQ02OQ01.companionMatrix
      (d := (minpoly ℝ M).natDegree) (minpoly ℝ M)
    -- Rewrite the coefficient using the key identity
    have hkey : ∀ m, ((X : ℝ[X]) ^ m %ₘ minpoly ℝ M).coeff k =
        C ^ m ⟨k, hk⟩ ⟨0, hd⟩ := fun m => coeff_pow_X_eq_companion M m k hk
    simp_rw [hkey]
    -- The entry series follows from the matrix exp series via norm bound
    apply Summable.of_norm_bounded (fun m => (|t| * ‖C‖) ^ m / m.factorial)
    · exact summable_pow_div_factorial _
    · intro m
      have hfact_pos : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr m.factorial_pos
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_of_pos hfact_pos,
          div_mul_eq_mul_div, div_le_div_right hfact_pos, mul_pow]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg t) m)
      calc |C ^ m ⟨k, hk⟩ ⟨0, hd⟩|
          = ‖C ^ m ⟨k, hk⟩ ⟨0, hd⟩‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖C ^ m ⟨k, hk⟩‖ := norm_le_pi_norm _ _
        _ ≤ ‖C ^ m‖ := norm_le_pi_norm _ _
        _ ≤ ‖C‖ ^ m := norm_pow_le C m
  · -- Case k ≥ d: the remainder polynomial has degree < d ≤ k, so coefficient k is 0
    push_neg at hk
    have hzero : ∀ m, ((X : ℝ[X]) ^ m %ₘ minpoly ℝ M).coeff k = 0 := fun m =>
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (Nat.lt_of_lt_of_le (modByMonic_natDegree_lt M m) hk)
    simp_rw [hzero, mul_zero]
    exact summable_zero

-- ============================================================
-- Section 2: Power Series for Matrix Exponential
-- ============================================================

/-- The matrix exponential is its power series: exp(t·M) = ∑_m (t^m/m!)·M^m. -/
theorem matrixExp_eq_tsum (t : ℝ) :
    exp ℝ (t • M) = ∑' m : ℕ, (t ^ m / (m.factorial : ℝ)) • M ^ m := by
  rw [exp_eq_tsum (𝕂 := ℝ) (𝔸 := Matrix n n ℝ)]
  apply tsum_congr; intro m
  rw [Algebra.smul_pow, smul_smul]
  congr 1; field_simp

-- ============================================================
-- Section 3: Basis Expansion of Matrix Powers
-- ============================================================

/-- Matrix power M^m equals the basis expansion ∑_{k<d} c_{m,k}·M^k. -/
theorem power_eq_basis_sum (m : ℕ) :
    M ^ m = ∑ k ∈ Finset.range (minpoly ℝ M).natDegree,
      ((X : ℝ[X]) ^ m %ₘ minpoly ℝ M).coeff k • M ^ k := by
  have heval := CayleyHamiltonOQ01.power_eq_aeval_mod_minpoly M m
  rw [heval, aeval_def, eval₂_eq_sum_range' (modByMonic_natDegree_lt M m)]
  simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

-- ============================================================
-- Section 4: Component-wise Interchange and Main Theorem
-- ============================================================

private lemma expPolyCoeff_summable_mul (k : ℕ) (t : ℝ) (v : ℝ) :
    Summable (fun m : ℕ =>
      (t ^ m / (m.factorial : ℝ)) * ((X : ℝ[X]) ^ m %ₘ minpoly ℝ M).coeff k * v) :=
  (expPolyCoeff_summable M k t).mul_right v

/-- Interchange of infinite series and finite sum at each matrix entry.
    Works entry-wise: for each (i,j), the real-valued series can be rearranged. -/
theorem exp_tsum_interchange (t : ℝ) :
    ∑' m : ℕ, (t ^ m / (m.factorial : ℝ)) • M ^ m =
    ∑ k ∈ Finset.range (minpoly ℝ M).natDegree, expPolyCoeff M k t • M ^ k := by
  -- Work component-wise: prove equality at each matrix entry
  apply Matrix.ext; intro i j
  -- Bring the tsum inside the matrix entry
  simp only [Matrix.tsum_apply, Matrix.smul_apply, Matrix.sum_apply]
  -- Replace M^m with its basis expansion
  simp_rw [power_eq_basis_sum M, Matrix.sum_apply, Matrix.smul_apply]
  -- LHS is now ∑' m, t^m/m! * ∑_k c_{m,k} * (M^k) i j
  simp_rw [Finset.mul_sum]
  -- Interchange ∑' m and ∑ k using tsum_sum (all series are summable)
  rw [tsum_sum (s := Finset.range (minpoly ℝ M).natDegree)]
  · congr 1; ext k
    -- Factor out (M^k) i j and identify with expPolyCoeff
    rw [← tsum_mul_right, expPolyCoeff]
    congr 1; ext m; ring
  · intro k _
    exact expPolyCoeff_summable_mul M k t ((M ^ k) i j)

/-- **Main Theorem**: The matrix exponential is a polynomial in M of degree < d.

    exp(t·M) = ∑_{k=0}^{d-1} p_k(t) · M^k

    where d = deg(minpoly ℝ M) and p_k(t) = ∑_{m≥0} (t^m/m!)·coeff_k(X^m mod μ).

    This proves exp(t·M) ∈ K[M] = span{I, M, ..., M^{d-1}}, the d-dimensional
    ℝ-algebra generated by M. -/
theorem matrixExp_poly_form (t : ℝ) :
    let d := (minpoly ℝ M).natDegree
    exp ℝ (t • M) = ∑ k ∈ Finset.range d, expPolyCoeff M k t • M ^ k := by
  rw [matrixExp_eq_tsum, exp_tsum_interchange]

-- ============================================================
-- Section 5: Corollaries
-- ============================================================

/-- The coefficient functions p_k are determined by the minimal polynomial.
    Two matrices with the same minimal polynomial share the same p_k. -/
theorem expPolyCoeff_depends_only_on_minpoly (M N : Matrix n n ℝ)
    (h : minpoly ℝ M = minpoly ℝ N) (k : ℕ) (t : ℝ) :
    expPolyCoeff M k t = expPolyCoeff N k t := by
  simp only [expPolyCoeff, h]

/-- exp(t·M) is in the ℝ-span of {I, M, ..., M^{d-1}}. -/
theorem matrixExp_in_span (t : ℝ) :
    exp ℝ (t • M) ∈ Submodule.span ℝ (Set.range (fun k : Fin (minpoly ℝ M).natDegree => M ^ (k : ℕ))) := by
  rw [matrixExp_poly_form]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact Set.mem_range.mpr ⟨⟨k, Finset.mem_range.mp hk⟩, rfl⟩

/-- exp(0) = 1 (identity matrix). -/
theorem matrixExp_zero_eq_one :
    exp ℝ (0 : Matrix n n ℝ) = 1 := exp_zero

/-- The degree bound: exp(t·M) uses at most n = Fintype.card n terms. -/
theorem matrixExp_atMost_n_terms (t : ℝ) :
    ∃ (coeffs : Fin (Fintype.card n) → ℝ),
      exp ℝ (t • M) = ∑ k : Fin (Fintype.card n), coeffs k • M ^ (k : ℕ) := by
  have hle : (minpoly ℝ M).natDegree ≤ Fintype.card n :=
    calc (minpoly ℝ M).natDegree
        ≤ M.charpoly.natDegree :=
          Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly M)
            (Matrix.charpoly_monic M).ne_zero
      _ = Fintype.card n := Matrix.charpoly_natDegree_eq_dim M
  refine ⟨fun k => if h : (k : ℕ) < (minpoly ℝ M).natDegree
    then expPolyCoeff M ↑k t else 0, ?_⟩
  rw [matrixExp_poly_form, Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp [Finset.mem_range.mp hk]

end CayleyHamiltonOQ01OQ03
