/-
  The upper Frobenius extreme is attained *only* by scalars: `dim_K C(M) = n² ↔ M scalar`
  (cayley-hamilton-cyclic-vector-all-fields-oq-02-oq-02)

  The sibling development pins down the whole Frobenius commutant range and both
  of its extremes, but characterises only the *lower* one:

    * `...OQ02OQ02Range.frobenius_commutant_range` — `n ≤ dim_K C(M) ≤ n²` for every
      `n × n` matrix `M` over a field `K`;
    * `...OQ02OQ02` — the lower bound `n` is attained **exactly** by the nonderogatory
      matrices (`dim_K C(M) = n ⟺ M nonderogatory`);
    * `...OQ02OQ02Scalar.finrank_centralizer_scalar` — the upper bound `n²` is
      attained *by* a scalar matrix `c • I` (`dim_K C(c • I) = n²`), one direction only.

  What was missing is the matching **converse for the upper extreme**: is a scalar
  matrix the *only* way to make the commutant maximal?  It is.  This file proves

    * `centralizer_eq_top_iff_scalar` — `C(M) = Mₙ(K)` (the commutant is everything)
      **iff** `M` is a scalar matrix `c • I`.  The reverse is the sibling
      `centralizer_scalar_eq_top`; the forward direction is the classical fact that a
      matrix commuting with *every* matrix — in particular with each single-entry
      matrix `single i j 1` (`Matrix.mem_range_scalar_iff_commute_single`) — must be a
      scalar.
    * `finrank_centralizer_eq_sq_iff_scalar` — the **dimension form** and headline of
      this file: `dim_K C(M) = n² ⟺ M = c • I` for some `c`.  A commutant of full
      dimension `n²` is a subspace of `Mₙ(K)` (itself of dimension `n²`), hence the
      whole space (`Submodule.eq_top_of_finrank_eq`); by the previous equivalence `M`
      is then scalar.

  Together with the lower-extreme characterisation this closes the description of the
  Frobenius range `n ≤ dim_K C(M) ≤ n²`: the bottom `n` is the nonderogatory locus, the
  top `n²` is exactly the (one-dimensional worth of) scalar matrices, and everything in
  between is genuinely derogatory-but-nonscalar.

  All results are `0`-sorry / `0`-axiom on top of Mathlib and the sibling files.
-/
import Mathlib
import Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ02OQ02Scalar

open Matrix Polynomial

noncomputable section

namespace CyclicCommutantScalarConverse

variable {K : Type*} [Field K] {n : ℕ}

/-- A single-entry matrix lies in the commutant of `M` exactly when it commutes
    with `M`; the convenient repackaging used below. -/
private theorem single_commute_of_mem_top
    {M : Matrix (Fin n) (Fin n) K}
    (htop : Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)) = ⊤)
    (i j : Fin n) : Commute (single i j 1) M := by
  have hmem : (single i j 1) ∈
      Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)) := by
    rw [htop]; exact Algebra.mem_top
  rw [Subalgebra.mem_centralizer_iff] at hmem
  exact (hmem M (Set.mem_singleton M)).symm

/-- **The commutant is everything iff the matrix is scalar.**  The centralizer of an
    `n × n` matrix `M` over a field is the *whole* matrix algebra exactly when `M` is a
    scalar matrix `c • I`:

      `C(M) = Mₙ(K) ⟺ ∃ c, M = c • I`.

    Reverse: a scalar commutes with everything (`centralizer_scalar_eq_top`).  Forward:
    if every matrix commutes with `M`, then in particular each single-entry matrix does,
    so `M` is in the range of the scalar embedding
    (`Matrix.mem_range_scalar_iff_commute_single`). -/
theorem centralizer_eq_top_iff_scalar (M : Matrix (Fin n) (Fin n) K) :
    Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)) = ⊤ ↔
      ∃ c : K, M = c • (1 : Matrix (Fin n) (Fin n) K) := by
  constructor
  · intro htop
    obtain ⟨c, hc⟩ := (Matrix.mem_range_scalar_iff_commute_single).mpr
      (fun i j _ => single_commute_of_mem_top htop i j)
    exact ⟨c, by rw [← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]⟩
  · rintro ⟨c, rfl⟩
    exact CyclicCommutantScalar.centralizer_scalar_eq_top c

/-- **Characterisation of the upper Frobenius extreme.**  For an `n × n` matrix `M` over
    a field `K`, the commutant has *maximal* dimension `n²` exactly when `M` is a scalar
    matrix:

      `dim_K C(M) = n² ⟺ ∃ c, M = c • I`.

    This is the exact converse of `...OQ02OQ02Scalar.finrank_centralizer_scalar` (which
    proves the `⟸` direction), and the dual of the lower-extreme characterisation
    `dim_K C(M) = n ⟺ M nonderogatory`.  Forward: a commutant of dimension `n²` fills the
    ambient `n²`-dimensional matrix algebra, so it *is* the whole algebra
    (`Submodule.eq_top_of_finrank_eq`), whence `M` is scalar by
    `centralizer_eq_top_iff_scalar`. -/
theorem finrank_centralizer_eq_sq_iff_scalar (M : Matrix (Fin n) (Fin n) K) :
    Module.finrank K
        ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))) = n * n ↔
      ∃ c : K, M = c • (1 : Matrix (Fin n) (Fin n) K) := by
  rw [← centralizer_eq_top_iff_scalar]
  constructor
  · intro hfin
    have htop : Subalgebra.toSubmodule
        (Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Subalgebra.finrank_toSubmodule, hfin, Module.finrank_matrix, Fintype.card_fin,
        Module.finrank_self, mul_one]
    -- transport `toSubmodule … = ⊤` back to the subalgebra
    apply le_antisymm le_top
    intro x _
    have : x ∈ Subalgebra.toSubmodule
        (Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))) := by
      rw [htop]; exact Submodule.mem_top
    rwa [Subalgebra.mem_toSubmodule] at this
  · intro htop
    rw [htop,
      LinearEquiv.finrank_eq
        (Subalgebra.topEquiv (R := K) (A := Matrix (Fin n) (Fin n) K)).toLinearEquiv,
      Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one]

/-- **The commutant is maximal-dimensional iff `M` is central.**  A reformulation of
    `finrank_centralizer_eq_sq_iff_scalar` in terms of the centre of the matrix algebra:
    `dim_K C(M) = n²` exactly when `M` lies in the range of the scalar embedding
    `Matrix.scalar`.  (`M ∈ Set.range (scalar (Fin n))` is the same condition as
    `∃ c, M = c • I`.) -/
theorem finrank_centralizer_eq_sq_iff_mem_range_scalar (M : Matrix (Fin n) (Fin n) K) :
    Module.finrank K
        ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))) = n * n ↔
      M ∈ Set.range (Matrix.scalar (Fin n)) := by
  rw [finrank_centralizer_eq_sq_iff_scalar]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]⟩

end CyclicCommutantScalarConverse

end
