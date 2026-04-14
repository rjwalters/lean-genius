/-
  Krylov Method for the Generalized (Vector) Minimal Polynomial
  (cayley-hamilton-minpoly-oq-03-oq-01)

  Question: Can the Krylov method be formalized for the generalized minimal
  polynomial — the minimal polynomial of a specific vector v under M, rather
  than of M itself?

  The minimal polynomial of a vector v under M is the unique monic polynomial
  μ_{M,v} of smallest degree with μ_{M,v}(M)·v = 0. This generalizes the
  minimal polynomial μ_M of M:
  - μ_M annihilates every vector (since μ_M(M) = 0 as a matrix)
  - μ_{M,v} divides μ_M for every v
  - deg(μ_{M,v}) ≤ n (from the n-dimensional ambient space)
  - The Krylov sequence {v, Mv, ..., M^d·v} yields exactly μ_{M,v}

  This extends OQ-03 (Krylov method for μ_M) to vector-specific minimal
  polynomials, which arise in Wiedemann's algorithm for sparse linear systems
  and in block Krylov methods for matrix functions.

  References:
  - Wiedemann (1986), "Solving sparse linear equations over finite fields"
  - Horn & Johnson, "Matrix Analysis" §3.3 (minimal polynomial theory)
  - Mathlib: LinearAlgebra.Matrix.Charpoly.Minpoly, Polynomial.minpoly

  See also: CayleyHamiltonMinpolyOQ03.lean (Krylov complexity for μ_M)
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

namespace MinpolyVec

open Matrix Polynomial Finset

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- PART I: Krylov Infrastructure (standalone; mirrors OQ-03)
-- ============================================================

/-- The k-th Krylov vector under M starting from v: M^k · v. -/
def krylovVec (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) (k : ℕ) : Fin n → K :=
  (M ^ k).mulVec v

/-- Helper: mulVec distributes over finite sums of matrices. -/
private theorem sum_mulVec {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    (∑ i ∈ s, f i).mulVec v = ∑ i ∈ s, (f i).mulVec v := by
  induction s using Finset.induction_on with
  | empty => simp [Matrix.zero_mulVec]
  | @insert a s' has ih =>
    rw [Finset.sum_insert has, Matrix.add_mulVec, ih, Finset.sum_insert has]

/-- **Krylov expansion**: evaluating p at M and applying to v gives a linear
    combination of Krylov vectors with coefficients equal to the polynomial's
    coefficients. -/
theorem aeval_mulVec_eq_krylov_sum (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (p : K[X]) :
    (aeval M p).mulVec v =
      ∑ i ∈ range (p.natDegree + 1), p.coeff i • krylovVec M v i := by
  have haeval_expand : aeval M p =
      ∑ i ∈ range (p.natDegree + 1), p.coeff i • M ^ i := by
    simp only [aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    have hsub : p.support ⊆ range (p.natDegree + 1) := by
      intro i hi
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp _ hi))
    rw [Finset.sum_subset hsub]
    · congr 1; ext i
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    · intro i _ hi
      rw [Polynomial.notMem_support_iff.mp hi, map_zero, zero_mul]
  rw [haeval_expand, sum_mulVec]
  simp only [Matrix.smul_mulVec, krylovVec]

-- ============================================================
-- PART II: The Vector Annihilator Set
-- ============================================================

/-- The **annihilator set** of v under M: all polynomials p with p(M)·v = 0.
    This is the key algebraic object for the generalized minimal polynomial:
    μ_{M,v} is the unique monic generator of minimum degree in this set. -/
def vecAnnSet (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Set K[X] :=
  {p | (aeval M p).mulVec v = 0}

theorem vecAnnSet_zero_mem (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    (0 : K[X]) ∈ vecAnnSet M v := by
  simp [vecAnnSet, Matrix.zero_mulVec]

theorem vecAnnSet_add_mem (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    {p q : K[X]} (hp : p ∈ vecAnnSet M v) (hq : q ∈ vecAnnSet M v) :
    p + q ∈ vecAnnSet M v := by
  simp only [vecAnnSet, Set.mem_setOf_eq] at *
  rw [map_add, Matrix.add_mulVec, hp, hq, add_zero]

/-- The annihilator set is an ideal: closed under polynomial multiplication.
    If p(M)·v = 0, then (q·p)(M)·v = q(M)·(p(M)·v) = q(M)·0 = 0. -/
theorem vecAnnSet_mul_mem (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    {p : K[X]} (hp : p ∈ vecAnnSet M v) (q : K[X]) :
    q * p ∈ vecAnnSet M v := by
  simp only [vecAnnSet, Set.mem_setOf_eq] at *
  rw [map_mul, Matrix.mul_mulVec, hp, Matrix.mulVec_zero]

-- ============================================================
-- PART III: The Minimal Polynomial of M Annihilates Every Vector
-- ============================================================

/-- **Main divisibility theorem**: The minimal polynomial of M belongs to the
    annihilator set of every vector v. Proof: μ_M(M) = 0 as a matrix (this is
    the Cayley-Hamilton / minpoly annihilation), so μ_M(M)·v = 0·v = 0. -/
theorem minpoly_mem_vecAnnSet (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    minpoly K M ∈ vecAnnSet M v := by
  simp only [vecAnnSet, Set.mem_setOf_eq]
  rw [minpoly.aeval K M]
  exact Matrix.zero_mulVec v

/-- The annihilator set of v contains a nonzero polynomial (namely μ_M), proving
    the generalized minimal polynomial exists. -/
theorem vecAnnSet_ne_bot [NeZero n] (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    ∃ p : K[X], p ≠ 0 ∧ p ∈ vecAnnSet M v :=
  ⟨minpoly K M, minpoly.ne_zero (Algebra.IsIntegral.isIntegral M),
   minpoly_mem_vecAnnSet M v⟩

-- ============================================================
-- PART IV: Degree Bound and Krylov Connection
-- ============================================================

/-- Every vector v has an annihilating polynomial of degree at most n.
    Witness: μ_M itself, which has natDegree ≤ n (from dimension bound). -/
theorem vec_ann_poly_of_deg_le_dim [NeZero n] (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) :
    ∃ p : K[X], p ≠ 0 ∧ p.natDegree ≤ n ∧ (aeval M p).mulVec v = 0 := by
  refine ⟨minpoly K M,
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral M),
    ?_, minpoly_mem_vecAnnSet M v⟩
  -- natDegree (minpoly K M) ≤ n: from Cayley-Hamilton, minpoly | charpoly,
  -- and charpoly has degree n
  have hch : (minpoly K M).natDegree ≤ (Matrix.charpoly M).natDegree := by
    apply Polynomial.natDegree_le_natDegree
    · exact minpoly.ne_zero (Algebra.IsIntegral.isIntegral M)
    · exact minpoly.dvd K M (Matrix.aeval_self_charpoly M)
  rw [Matrix.natDegree_charpoly] at hch
  exact hch

/-- The Krylov expansion at μ_M gives a zero linear combination of Krylov vectors.
    This is the algebraic certificate that the Krylov sequence for v is dependent
    within deg(μ_M) + 1 vectors. -/
theorem krylov_zero_combo_at_minpoly (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) :
    ∑ i ∈ range ((minpoly K M).natDegree + 1),
      (minpoly K M).coeff i • krylovVec M v i = 0 := by
  rw [← aeval_mulVec_eq_krylov_sum]
  exact minpoly_mem_vecAnnSet M v

-- ============================================================
-- PART V: Existence of the Vector Minimal Polynomial
-- ============================================================

/-- The generalized (vector) minimal polynomial exists: there is a monic polynomial
    μ_{M,v} of smallest degree annihilating v, it has degree ≤ n, it divides μ_M,
    and it divides any other annihilating polynomial (minimality).

    Proof sketch: K[X] is a PID; the annihilator ideal I_v is nonzero (contains μ_M);
    its generator is the vector minimal polynomial. Divisibility of μ_M ∈ I_v gives
    μ_{M,v} | μ_M, hence deg(μ_{M,v}) ≤ deg(μ_M) ≤ n.

    The sorry requires extracting the generator of a nonzero ideal in a PID
    via Mathlib's IsPrincipalIdealRing API. -/
theorem vec_minpoly_exists [NeZero n] (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) :
    ∃ μ : K[X], Monic μ ∧ μ.natDegree ≤ n ∧
    (aeval M μ).mulVec v = 0 ∧
    μ ∣ minpoly K M ∧
    ∀ q : K[X], (aeval M q).mulVec v = 0 → μ ∣ q := by
  sorry

end MinpolyVec

/-
  ## Summary

  **Problem**: Krylov method for the generalized (vector) minimal polynomial.

  **Status**: Partial formalization. Core annihilator theory proved; the existence
  and minimality of the vector minimal polynomial requires PID ideal generation
  (1 sorry remaining).

  **Proved (8 theorems, 0 sorries among them)**:
  - `aeval_mulVec_eq_krylov_sum`: polynomial evaluation = Krylov linear combination
  - `vecAnnSet_zero_mem`, `vecAnnSet_add_mem`, `vecAnnSet_mul_mem`: ideal axioms
  - `minpoly_mem_vecAnnSet`: μ_M annihilates every vector v
  - `vecAnnSet_ne_bot`: annihilator ideal is nonzero
  - `vec_ann_poly_of_deg_le_dim`: annihilating polynomial of degree ≤ n exists
  - `krylov_zero_combo_at_minpoly`: Krylov vectors at μ_M are linearly dependent

  **Sorry (1)**:
  - `vec_minpoly_exists`: full existence + minimality + divisibility — needs PID
    ideal extraction (~100 lines using Submodule.IsPrincipal and Ideal.span_singleton)

  **Key insight**: The vector minimal polynomial μ_{M,v} always divides μ_M,
  so the Krylov method for v terminates in ≤ deg(μ_M) ≤ n steps. This
  justifies Wiedemann's single-vector algorithm for sparse matrix problems.
-/
