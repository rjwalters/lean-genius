/-
  Commutant Characterization: A Cyclic Vector Forces the Centralizer to be K[M]
  (cayley-hamilton-cyclic-vector-all-fields-oq-02)

  The parent theorem (CayleyHamiltonCyclicVectorAllFields.lean) and its converse
  (CayleyHamiltonCyclicVectorAllFieldsOQ01OQ01.lean) establish the biconditional

    IsNonderogatory M ↔ ∃ v, IsCyclicVector M v.

  This file proves the third classical characterization of nonderogatory matrices
  (Hoffman & Kunze, "Linear Algebra" §7.5; Roman, "Advanced Linear Algebra" §10.4):

    **If M has a cyclic vector then every matrix commuting with M is a
    polynomial in M.**

  Equivalently, the commutant (centralizer) of M coincides exactly with the
  algebra K[M] of polynomials in M, and is therefore commutative.

  ## Proof

  Let v be a cyclic vector for the n×n matrix M over a field K.

  1. The Krylov vectors {v, Mv, …, M^{n-1}v} are linearly independent
     (this is the converse of the cyclic-vector characterization, and is the
     content of `krylov_linearIndependent`, mirrored from the infinite-field
     backward file). Being n independent vectors in the n-dimensional space
     Kⁿ, they form a basis `b`.

  2. Let A commute with M. Express the single vector A·v in the Krylov basis:
       A·v = ∑_{k<n} cₖ (Mᵏ·v),     cₖ = b.repr (A·v) k.
     Set p := ∑_{k<n} cₖ Xᵏ. Then p(M)·v = ∑ cₖ Mᵏ·v = A·v.

  3. A and p(M) agree on every basis vector Mⁱ·v:
       A·(Mⁱ·v) = Mⁱ·(A·v)        [A commutes with Mⁱ]
                 = Mⁱ·(p(M)·v)     [step 2]
                 = p(M)·(Mⁱ·v)     [p(M) commutes with Mⁱ].
     Since the Krylov vectors span Kⁿ, A·w = p(M)·w for all w, hence A = p(M)
     (a matrix is determined by its action, recovered column-by-column).

  ## Status: 0 sorries, 0 axioms (machine-verified under Docker, full build,
  7745 jobs, Mathlib v4.26.0).
-/
import Mathlib
import Proofs.CayleyHamiltonCyclicVectorAllFields

noncomputable section

namespace CyclicCommutant

open Matrix Polynomial GeneralCyclicVector

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- SECTION I: Krylov vectors of a cyclic vector are independent
-- ============================================================

/-- If `v` is a cyclic vector for `M` (no nonzero polynomial of degree `< n`
    annihilates `v`), then the Krylov vectors `{Mᵏ·v}_{k<n}` are linearly
    independent. Mirrored from the infinite-field backward direction
    (`Nonderogatory.Backward.linearIndependent_of_isCyclicVector`). -/
theorem krylov_linearIndependent
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hv : IsCyclicVector M v) (hn : 0 < n) :
    LinearIndependent K (fun k : Fin n => (M ^ (k : ℕ)).mulVec v) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  set p := ∑ k : Fin n, C (c k) * X ^ (k : ℕ) with hp_def
  have hp_aeval : aeval M p = ∑ k : Fin n, c k • M ^ (k : ℕ) := by
    simp only [p, map_sum, map_mul, map_pow, aeval_C, aeval_X,
               Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hp_ann : (aeval M p).mulVec v = 0 := by
    rw [hp_aeval]
    have : (∑ k : Fin n, c k • M ^ (k : ℕ)).mulVec v =
           ∑ k : Fin n, c k • (M ^ (k : ℕ)).mulVec v := by
      simp only [Matrix.sum_mulVec, Matrix.smul_mulVec]
    rw [this, hc]
  have hp_deg : p.natDegree < n := by
    apply lt_of_le_of_lt (natDegree_sum_le _ _)
    apply (Finset.sup_lt_iff (by omega : (0 : ℕ) < n)).mpr
    intro k _; exact lt_of_le_of_lt (natDegree_C_mul_X_pow_le (c k) ↑k) k.isLt
  have hp_zero : p = 0 := hv p hp_deg hp_ann
  have h_coeff := congr_arg (Polynomial.coeff · ↑i) hp_zero
  simp only [Polynomial.coeff_zero, p, C_mul_X_pow_eq_monomial,
             finset_sum_coeff, coeff_monomial] at h_coeff
  simpa [Fin.val_injective.eq_iff] using h_coeff

-- ============================================================
-- SECTION II: Polynomials in M commute with powers of M
-- ============================================================

/-- `p(M)` commutes with `Mʲ` in the matrix ring (polynomials in `M` commute
    with powers of `M`). -/
private lemma aeval_commute_pow (p : K[X]) (M : Matrix (Fin n) (Fin n) K) (j : ℕ) :
    aeval M p * M ^ j = M ^ j * aeval M p := by
  have hcomm : Commute (aeval M p) M := by
    show aeval M p * M = M * aeval M p
    have h : aeval M p * aeval M (X : K[X]) = aeval M (X : K[X]) * aeval M p := by
      rw [← map_mul, ← map_mul, mul_comm p X]
    simpa [aeval_X] using h
  exact hcomm.pow_right j

-- ============================================================
-- SECTION III: Main theorem — commuting matrices are polynomials in M
-- ============================================================

/-- **Commutant characterization.** If `M` has a cyclic vector `v` and `A`
    commutes with `M`, then `A` is a polynomial in `M`: there is `p` with
    `A = aeval M p`.

    This is the structural heart of the nonderogatory theory: a cyclic vector
    forces the centralizer of `M` to be exactly the algebra `K[M]`. -/
theorem commuting_matrix_is_polynomial
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hcyc : IsCyclicVector M v)
    (A : Matrix (Fin n) (Fin n) K) (hA : A * M = M * A) :
    ∃ p : K[X], A = aeval M p := by
  -- Degenerate 0×0 case: every matrix is the unique 0×0 matrix.
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, Subsingleton.elim _ _⟩
  -- Krylov vectors form a basis of Kⁿ.
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hli : LinearIndependent K (fun k : Fin n => (M ^ (k : ℕ)).mulVec v) :=
    krylov_linearIndependent M v hcyc hn
  set b : Module.Basis (Fin n) K (Fin n → K) :=
    basisOfLinearIndependentOfCardEqFinrank hli
      (Module.finrank_fintype_fun_eq_card K).symm with hb_def
  have hb : ∀ i, b i = (M ^ (i : ℕ)).mulVec v := by
    intro i; rw [hb_def, coe_basisOfLinearIndependentOfCardEqFinrank]
  -- The polynomial whose coordinates are those of A·v in the Krylov basis.
  refine ⟨∑ k : Fin n, C (b.repr (A.mulVec v) k) * X ^ (k : ℕ), ?_⟩
  set p : K[X] := ∑ k : Fin n, C (b.repr (A.mulVec v) k) * X ^ (k : ℕ) with hp_def
  -- p(M) = ∑ (coords) • Mᵏ.
  have hp_aeval : aeval M p = ∑ k : Fin n, b.repr (A.mulVec v) k • M ^ (k : ℕ) := by
    simp only [p, map_sum, map_mul, map_pow, aeval_C, aeval_X,
               Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  -- p(M)·v = A·v  (Basis.sum_repr).
  have hAv : (aeval M p).mulVec v = A.mulVec v := by
    rw [hp_aeval]
    have hdist : (∑ k : Fin n, b.repr (A.mulVec v) k • M ^ (k : ℕ)).mulVec v =
        ∑ k : Fin n, b.repr (A.mulVec v) k • (M ^ (k : ℕ)).mulVec v := by
      simp only [Matrix.sum_mulVec, Matrix.smul_mulVec]
    rw [hdist,
        show (∑ k : Fin n, b.repr (A.mulVec v) k • (M ^ (k : ℕ)).mulVec v) =
             ∑ k : Fin n, b.repr (A.mulVec v) k • b k from
          Finset.sum_congr rfl (fun k _ => by rw [hb k])]
    exact b.sum_repr (A.mulVec v)
  -- A and p(M) agree on every basis vector.
  have key : ∀ i : Fin n, A.mulVec (b i) = (aeval M p).mulVec (b i) := by
    intro i
    have e1 : A.mulVec ((M ^ (i : ℕ)).mulVec v) =
        (M ^ (i : ℕ)).mulVec (A.mulVec v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      exact Commute.pow_right hA (i : ℕ)
    have e2 : (aeval M p).mulVec ((M ^ (i : ℕ)).mulVec v) =
        (M ^ (i : ℕ)).mulVec ((aeval M p).mulVec v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      exact aeval_commute_pow p M i
    rw [hb i, e1, e2, hAv]
  -- A and p(M) agree on every vector (basis spans), hence are equal.
  have hall : ∀ w, A.mulVec w = (aeval M p).mulVec w := by
    intro w
    have hlinA : A.mulVec w = ∑ i, b.repr w i • A.mulVec (b i) := by
      conv_lhs => rw [← b.sum_repr w]
      rw [← Matrix.mulVecLin_apply, map_sum]
      simp only [map_smul, Matrix.mulVecLin_apply]
    have hlinP : (aeval M p).mulVec w = ∑ i, b.repr w i • (aeval M p).mulVec (b i) := by
      conv_lhs => rw [← b.sum_repr w]
      rw [← Matrix.mulVecLin_apply, map_sum]
      simp only [map_smul, Matrix.mulVecLin_apply]
    rw [hlinA, hlinP]
    exact Finset.sum_congr rfl (fun i _ => by rw [key i])
  -- Recover the matrix equality column-by-column.
  ext i j
  have h := congr_fun (hall (Pi.single j 1)) i
  simpa only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
             Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

-- ============================================================
-- SECTION IV: Consequences
-- ============================================================

/-- The centralizer of a matrix with a cyclic vector is **commutative**: any two
    matrices commuting with `M` commute with each other, since both are
    polynomials in `M`. -/
theorem commutant_commutative
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hcyc : IsCyclicVector M v)
    (A B : Matrix (Fin n) (Fin n) K)
    (hA : A * M = M * A) (hB : B * M = M * B) :
    A * B = B * A := by
  obtain ⟨p, rfl⟩ := commuting_matrix_is_polynomial M v hcyc A hA
  obtain ⟨q, rfl⟩ := commuting_matrix_is_polynomial M v hcyc B hB
  rw [← map_mul, ← map_mul, mul_comm]

/-- Every polynomial in `M` commutes with `M` — the trivial inclusion
    `K[M] ⊆ centralizer(M)`. Together with `commuting_matrix_is_polynomial`
    this gives the full equality of the centralizer with `K[M]`. -/
theorem aeval_commute (M : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    aeval M p * M = M * aeval M p := by
  simpa using aeval_commute_pow p M 1

end CyclicCommutant

end
