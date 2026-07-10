/-
  The maximally-derogatory extreme: the commutant of a scalar matrix is everything
  (cayley-hamilton-cyclic-vector-all-fields-oq-02-oq-02)

  The sibling file `...OQ02OQ02` proves the headline **equality case** of the Frobenius
  commutant bound `n ≤ dim_K C(M) ≤ n²`:

      `C(M) = K[M] ⟺ M nonderogatory`,   and   `dim_K C(M) = n` for nonderogatory `M`,

  i.e. a nonderogatory matrix has the *smallest possible* commutant.  This file records
  the opposite, **maximally-derogatory extreme**: a scalar matrix `c • I` commutes with
  *everything*, so its commutant is the whole matrix algebra and attains the *largest
  possible* dimension `n²`.

    * `centralizer_scalar_eq_top` — for any `c : K`, `C(c • I) = ⊤`, the whole algebra
      `Mₙ(K)`.  (Scalars are central: `(c • I) N = c • N = N (c • I)`.)
    * `adjoin_scalar_eq_bot` — `K[c • I] = ⊥`, the scalar subalgebra, since `c • I` is
      already in the image of `algebraMap K Mₙ(K)`.
    * `finrank_centralizer_scalar` — `dim_K C(c • I) = n²`, the top of the Frobenius
      range (contrast the nonderogatory value `n`).
    * `scalar_derogatory` — for `n ≥ 2`, `c • I` is **derogatory**
      (`minpoly K (c • I) ≠ charpoly (c • I)`).  It is a concrete witness that the
      Frobenius bound `dim_K C(M) ≥ n` is *not* an equality in general: here the
      commutant has dimension `n² > n`.  (Obtained purely from the sibling headline:
      were `c • I` nonderogatory its commutant would have dimension `n`, but it has
      dimension `n²`.)
    * `finrank_centralizer_scalar_gt` — the quantitative form: for `n ≥ 2`,
      `n < dim_K C(c • I)`, i.e. the Frobenius lower bound is *strictly* exceeded at
      the derogatory extreme.

  Together with `...OQ02OQ02` (dimension `n`, nonderogatory) and its `...Masa`
  refinement, this pins both ends of the interval `n ≤ dim_K C(M) ≤ n²`:
  `n` is realised by nonderogatory matrices, `n²` by scalar matrices.

  All results are `0`-sorry / `0`-axiom on top of Mathlib and the sibling files.
-/
import Mathlib
import Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ02OQ02

open Matrix Polynomial

noncomputable section

namespace CyclicCommutantScalar

variable {K : Type*} [Field K] {n : ℕ}

/-- **Scalar matrices are central.**  For any `c : K`, every `n × n` matrix commutes
    with `c • I`, so the commutant of `c • I` is the whole algebra `Mₙ(K)`. -/
theorem centralizer_scalar_eq_top (c : K) :
    Subalgebra.centralizer K
        ({c • (1 : Matrix (Fin n) (Fin n) K)} : Set (Matrix (Fin n) (Fin n) K)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  rw [Subalgebra.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  rw [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-- **Polynomials in a scalar are just scalars.**  `K[c • I] = ⊥`: since
    `c • I = algebraMap K Mₙ(K) c` already lies in the scalar subalgebra `⊥`, adjoining
    it adds nothing. -/
theorem adjoin_scalar_eq_bot (c : K) :
    Algebra.adjoin K
        ({c • (1 : Matrix (Fin n) (Fin n) K)} : Set (Matrix (Fin n) (Fin n) K)) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Algebra.adjoin_le
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  rw [SetLike.mem_coe, Algebra.mem_bot]
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]⟩

/-- **Commutant dimension at the derogatory extreme.**  `dim_K C(c • I) = n²`, the top
    of the Frobenius range `n ≤ dim_K C(M) ≤ n²`.  (Contrast the nonderogatory value
    `dim_K C(M) = n` from the sibling headline.) -/
theorem finrank_centralizer_scalar (c : K) :
    Module.finrank K
        ↥(Subalgebra.centralizer K
            ({c • (1 : Matrix (Fin n) (Fin n) K)} : Set (Matrix (Fin n) (Fin n) K)))
      = n * n := by
  rw [centralizer_scalar_eq_top,
    LinearEquiv.finrank_eq
      (Subalgebra.topEquiv (R := K) (A := Matrix (Fin n) (Fin n) K)).toLinearEquiv,
    Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one]

/-- **Scalar matrices are derogatory for `n ≥ 2`.**  A concrete witness that the
    Frobenius bound `dim_K C(M) ≥ n` is strict in general: were `c • I` nonderogatory,
    its commutant would have dimension `n` (sibling headline), but in fact
    `dim_K C(c • I) = n² > n`.  Hence `minpoly K (c • I) ≠ charpoly (c • I)`. -/
theorem scalar_derogatory (c : K) (hn : 2 ≤ n) :
    minpoly K (c • (1 : Matrix (Fin n) (Fin n) K))
      ≠ (c • (1 : Matrix (Fin n) (Fin n) K)).charpoly := by
  intro hM
  have h1 :=
    CyclicCommutantDimension.finrank_centralizer_eq_of_nonderogatory
      (c • (1 : Matrix (Fin n) (Fin n) K)) hM
  rw [finrank_centralizer_scalar] at h1
  -- `h1 : n * n = n`, impossible for `n ≥ 2` since `2 * n ≤ n * n`.
  have h2 : 2 * n ≤ n * n := Nat.mul_le_mul hn (le_refl n)
  omega

/-- **The Frobenius lower bound is strict at the derogatory extreme.**  For `n ≥ 2`
    the commutant of a scalar matrix `c • I` has dimension `n² > n`, so the bound
    `dim_K C(M) ≥ n` (equality iff `M` nonderogatory) is *strictly* exceeded here:

      `n < dim_K C(c • I)`.

    This is the quantitative companion of `scalar_derogatory` (which records only
    the qualitative failure `minpoly ≠ charpoly`): a scalar matrix is not merely
    derogatory, its commutant is maximally large. -/
theorem finrank_centralizer_scalar_gt (c : K) (hn : 2 ≤ n) :
    n < Module.finrank K
        ↥(Subalgebra.centralizer K
            ({c • (1 : Matrix (Fin n) (Fin n) K)} : Set (Matrix (Fin n) (Fin n) K))) := by
  rw [finrank_centralizer_scalar]
  have h2 : 2 * n ≤ n * n := Nat.mul_le_mul hn (le_refl n)
  omega

end CyclicCommutantScalar
