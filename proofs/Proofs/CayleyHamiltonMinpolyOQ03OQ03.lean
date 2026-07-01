/-
# Krylov Sequences and the Rational Canonical Form

This file is the structural follow-up to `CayleyHamiltonMinpolyOQ03.lean`
(problem `cayley-hamilton-minpoly-oq-03`), which showed that the Krylov
sequence `v, Mv, M²v, …` of a matrix `M` goes linearly dependent exactly at
step `d = deg μ_M`.  Here we answer: *what does the Krylov basis reveal about
`M` itself?*

The answer is the **companion / rational-canonical-form** statement.  Assemble
the first `n` Krylov vectors as the columns of a change-of-basis matrix

    P = ( v ∣ Mv ∣ ⋯ ∣ M^{n-1}v ),   `krylovMatrix M v`,

and let `C(μ_M)` be the companion matrix of the (monic, degree-`n`) minimal
polynomial.  Then the Krylov iteration **intertwines** `M` with the companion
matrix:

    M · P  =  P · C(μ_M).                     (`krylov_companion_conjugation`)

This holds for *every* starting vector `v` once `M` is nonderogatory
(`deg μ_M = n`): the identity is a coordinate-free consequence of the two facts
`M·(M^k v) = M^{k+1} v` and `μ_M(M)·v = 0`.  When in addition `v` is cyclic the
Krylov vectors form a basis, `P` is invertible, and conjugation upgrades to a
genuine **similarity**

    P⁻¹ · M · P  =  C(μ_M),                    (`krylov_rcf_similarity`)

exhibiting the rational canonical form of a nonderogatory matrix as a single
companion block.  This is the constructive bridge — via the same `O(n³)` Krylov
iteration already formalized — from numerical linear algebra to the
module-theoretic normal form that classifies matrices up to similarity over an
arbitrary field.

## Main results

* `krylovMatrix`, `companion` — the change-of-basis and companion matrices.
* `krylov_companion_conjugation` — `M * P = P * C(μ_M)` (nonderogatory).
* `krylov_rcf_similarity` — `P⁻¹ * M * P = C(μ_M)` when `P` is invertible.
* `krylovMatrix_isUnit_of_cyclic` — a cyclic vector makes `P` invertible.
* `krylov_rcf_similarity_of_cyclic` — the RCF similarity from a cyclic vector.

All results are proved with `0` sorries and no additional axioms.
-/
import Proofs.CayleyHamiltonMinpolyOQ03

namespace MinpolyComplexity

open Matrix Polynomial Finset

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- PART I: The companion matrix and the Krylov change-of-basis
-- ============================================================

/-- The **companion matrix** of a polynomial `μ`, in the convention where the
    coefficients occupy the last column and the subdiagonal carries `1`s:

    ```
    0 0 … 0 -a₀
    1 0 … 0 -a₁
    0 1 … 0 -a₂
    ⋮       ⋮
    0 0 … 1 -a_{n-1}
    ```

    For a monic `μ = Xⁿ + a_{n-1}Xⁿ⁻¹ + ⋯ + a₀` of degree `n`, this is exactly
    the matrix of multiplication-by-`X` on `K[X]/(μ)` in the basis
    `1, X, …, Xⁿ⁻¹`. -/
def companion (μ : K[X]) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j =>
    if (j : ℕ) + 1 = n then -μ.coeff (i : ℕ)
    else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0

/-- The **Krylov change-of-basis matrix**: column `j` is the `j`-th Krylov
    vector `Mʲ v`.  When `v` is cyclic and `M` nonderogatory this is the
    matrix `P = (v ∣ Mv ∣ ⋯ ∣ M^{n-1}v)` that conjugates `M` into rational
    canonical form. -/
def krylovMatrix (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => krylovVec M v (j : ℕ) i

@[simp]
theorem krylovMatrix_apply (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (i j : Fin n) : krylovMatrix M v i j = krylovVec M v (j : ℕ) i := rfl

-- ============================================================
-- PART II: The conjugation identity  M · P = P · C(μ_M)
-- ============================================================

/-- **Krylov–companion conjugation.**  For a nonderogatory matrix `M`
    (`deg μ_M = n`) and *any* starting vector `v`, the Krylov change-of-basis
    matrix `P` intertwines `M` with the companion matrix of the minimal
    polynomial:

        `M * P = P * C(μ_M)`.

    Columnwise this says `M·(Mʲv) = M^{j+1}v`, which for `j < n-1` is the
    subdiagonal shift of `C`, and for `j = n-1` is `M^n v = -∑_{k<n} a_k M^k v`
    (Cayley–Hamilton applied to `v`), the last column of `C`. -/
theorem krylov_companion_conjugation [NeZero n]
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hdeg : (minpoly K M).natDegree = n) :
    M * krylovMatrix M v = krylovMatrix M v * companion (minpoly K M) := by
  -- Cayley–Hamilton for `v`: `∑_{i≤n} aᵢ (Mⁱv) = 0`.
  have hann : (∑ i ∈ range (n + 1), (minpoly K M).coeff i • krylovVec M v i) = 0 := by
    have h1 := minpoly_annihilates_vec M v
    rw [aeval_mulVec_eq_krylov_sum, hdeg] at h1
    exact h1
  -- Leading coefficient is `1`.
  have hmonic : (minpoly K M).coeff n = 1 := by
    have h := (minpoly.monic (isIntegral M)).coeff_natDegree
    rwa [hdeg] at h
  -- Peel the top term: `∑_{k<n} a_k (Mᵏv) = -(Mⁿv)`.
  have hsplit : (∑ k ∈ range n, (minpoly K M).coeff k • krylovVec M v k)
      = - krylovVec M v n := by
    rw [Finset.sum_range_succ, hmonic, one_smul] at hann
    exact eq_neg_of_add_eq_zero_left hann
  ext i j
  -- Left-hand column `j`:  `M·(Mʲv) = M^{j+1}v`.
  have hL : (M * krylovMatrix M v) i j = krylovVec M v ((j : ℕ) + 1) i := by
    rw [Matrix.mul_apply, krylovVec_succ]
    simp only [krylovMatrix, Matrix.of_apply, Matrix.mulVec, dotProduct]
  rw [hL, Matrix.mul_apply]
  simp only [krylovMatrix, companion, Matrix.of_apply]
  by_cases hjn : (j : ℕ) + 1 = n
  · -- Last column: use Cayley–Hamilton to identify `M^{j+1}v = Mⁿv`.
    simp only [if_pos hjn]
    rw [hjn]
    have key : (∑ k ∈ range n, krylovVec M v k i * (minpoly K M).coeff k)
        = - krylovVec M v n i := by
      have h := congrFun hsplit i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at h
      rw [← h]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [Fin.sum_univ_eq_sum_range
      (fun k => krylovVec M v k i * -(minpoly K M).coeff k) n]
    simp only [mul_neg, Finset.sum_neg_distrib]
    rw [key]; ring
  · -- Interior column `j`: only the `k = j+1` term survives (the subdiagonal `1`).
    have hlt : (j : ℕ) + 1 < n :=
      lt_of_le_of_ne (Nat.succ_le_of_lt j.isLt) hjn
    have hj'val : ((⟨(j : ℕ) + 1, hlt⟩ : Fin n) : ℕ) = (j : ℕ) + 1 := rfl
    simp only [if_neg hjn]
    rw [Finset.sum_eq_single_of_mem (⟨(j : ℕ) + 1, hlt⟩ : Fin n)
        (Finset.mem_univ _) (by
          intro k _ hk
          have hne : (k : ℕ) ≠ (j : ℕ) + 1 := fun hc =>
            hk (Fin.ext (hc.trans hj'val.symm))
          rw [if_neg hne, mul_zero])]
    rw [hj'val, if_pos rfl, mul_one]

-- ============================================================
-- PART III: The similarity  P⁻¹ · M · P = C(μ_M)
-- ============================================================

/-- **Rational canonical form via Krylov.**  When the Krylov change-of-basis
    matrix `P` is invertible, conjugation `M·P = P·C(μ_M)` upgrades to a
    similarity `P⁻¹·M·P = C(μ_M)`: the matrix `M` is similar to the companion
    matrix of its minimal polynomial, i.e. it is in rational canonical form
    (a single companion block). -/
theorem krylov_rcf_similarity [NeZero n]
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hdeg : (minpoly K M).natDegree = n)
    (hunit : IsUnit (krylovMatrix M v).det) :
    (krylovMatrix M v)⁻¹ * M * krylovMatrix M v = companion (minpoly K M) := by
  have hconj := krylov_companion_conjugation M v hdeg
  rw [Matrix.mul_assoc, hconj, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit,
    Matrix.one_mul]

-- ============================================================
-- PART IV: A cyclic vector makes the Krylov matrix invertible
-- ============================================================

/-- The columns of the Krylov matrix are precisely the Krylov vectors. -/
theorem krylovMatrix_col (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    (krylovMatrix M v).col = fun i : Fin n => krylovVec M v i := by
  funext j i; rfl

/-- **Invertibility from a cyclic vector.**  For a nonderogatory matrix
    (`μ_M = χ_M`) with a cyclic vector `v`, the `n` Krylov vectors are linearly
    independent (parent theorem `nonderogatory_krylov_optimal`), so the Krylov
    change-of-basis matrix is invertible. -/
theorem krylovMatrix_isUnit_of_cyclic [NeZero n]
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hcyclic : ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0)
    (hnond : minpoly K M = M.charpoly) :
    IsUnit (krylovMatrix M v).det := by
  have hli := nonderogatory_krylov_optimal M v hcyclic hnond
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit,
    krylovMatrix_col]
  exact hli

/-- **Rational canonical form of a nonderogatory matrix.**  Combining the
    conjugation identity with invertibility of the Krylov matrix: a
    nonderogatory matrix with a cyclic vector is conjugate to the companion
    matrix of its minimal (= characteristic) polynomial via the explicit Krylov
    change of basis `P = (v ∣ Mv ∣ ⋯ ∣ M^{n-1}v)`. -/
theorem krylov_rcf_similarity_of_cyclic [NeZero n]
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hcyclic : ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0)
    (hnond : minpoly K M = M.charpoly)
    (hdeg : (minpoly K M).natDegree = n) :
    (krylovMatrix M v)⁻¹ * M * krylovMatrix M v = companion (minpoly K M) :=
  krylov_rcf_similarity M v hdeg (krylovMatrix_isUnit_of_cyclic M v hcyclic hnond)

end MinpolyComplexity
