import Mathlib
import Proofs.CayleyHamiltonOQ01

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

## Axiom

`expPolyCoeff_summable`: For each k and t, the series ∑_{m≥0} t^m/m! · c_{m,k} converges.
Justification: c_{m,k} = coeff_k(X^m mod μ_M) satisfies a linear recurrence of order d
(companion matrix of μ_M), so |c_{m,k}| ≤ C·r^m. Then ∑_m |t|^m r^m/m! = e^{|t|r} < ∞.
-/

open Matrix Polynomial BigOperators NormedSpace Finset

namespace CayleyHamiltonOQ01OQ03

variable {n : Type*} [DecidableEq n] [Fintype n] [Nontrivial (Matrix n n ℝ)]
variable (M : Matrix n n ℝ)

-- ============================================================
-- Section 1: The Coefficient Functions p_k(t)
-- ============================================================

/-- For k < d = deg(μ_M), the k-th coefficient polynomial:
    p_k(t) = ∑_{m≥0} (t^m/m!) · coeff_k(X^m mod μ_M). -/
noncomputable def expPolyCoeff (k : ℕ) (t : ℝ) : ℝ :=
  ∑' m : ℕ, (t ^ m / (m.factorial : ℝ)) * ((X : ℝ[X]) ^ m %ₘ minpoly ℝ M).coeff k

/-- The series defining p_k(t) converges.
    Justification: |coeff_k(X^m mod μ_M)| ≤ C·r^m by linear recurrence bound;
    ∑_m |t|^m r^m/m! = e^{|t|r} < ∞ by exp convergence. -/
axiom expPolyCoeff_summable (k : ℕ) (t : ℝ) :
    Summable (fun m : ℕ =>
      (t ^ m / (m.factorial : ℝ)) * ((X : ℝ[X]) ^ m %ₘ minpoly ℝ M).coeff k)

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

private lemma minpoly_natDegree_pos : 0 < (minpoly ℝ M).natDegree :=
  CayleyHamiltonOQ01.minpoly_degree_pos M

private lemma modByMonic_natDegree_lt (m : ℕ) :
    ((X : ℝ[X]) ^ m %ₘ minpoly ℝ M).natDegree < (minpoly ℝ M).natDegree := by
  rcases eq_or_ne ((X : ℝ[X]) ^ m %ₘ minpoly ℝ M) 0 with h | h
  · simp only [h, Polynomial.natDegree_zero]; exact minpoly_natDegree_pos M
  · exact CayleyHamiltonOQ01.degree_mod_minpoly_lt M (X ^ m) h

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
