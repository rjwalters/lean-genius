/-
  Dimension of the commutant: `dim_K C(M) = n` for nonderogatory `M`
  (cayley-hamilton-cyclic-vector-all-fields-oq-02-oq-02)

  The triple equivalence for a single `n × n` matrix `M` over a field `K`
  (Hoffman & Kunze §7.5, Roman §10.4) links

      (i)   `M` admits a cyclic vector
      (ii)  `M` is nonderogatory  (`minpoly K M = charpoly M`)
      (iii) the centralizer `C(M) = {N : NM = MN}` equals `K[M] = Algebra.adjoin K {M}`.

  The sibling development supplies:
    * `CyclicCommutant.commuting_matrix_is_polynomial` — the forward edge
      **(i) ⟹ (iii)** (a cyclic vector forces every commuting matrix to be a
      polynomial in `M`);
    * `CyclicCommutantConverse.centralizer_eq_adjoin_implies_nonderogatory` — the
      converse edge **(iii) ⟹ (ii)**;
    * `CyclicVectorBiconditional.nonderogatory_iff_has_cyclic_vector` — **(ii) ⟺ (i)**;
    * `CyclicCommutantConverse.finrank_adjoin_eq_natDegree_minpoly` —
      `dim_K K[M] = deg(minpoly K M)`;
    * `CyclicCommutantConverse.finrank_centralizer_ge` — the Frobenius bound
      `n ≤ dim_K C(M)`.

  This file closes the **(ii) ⟹ (iii)** edge, packaging the full biconditional
  `C(M) = K[M] ⟺ M nonderogatory`, and draws the headline **dimension count**:

      for a nonderogatory `M`,      `dim_K C(M) = n`.

  Indeed a nonderogatory `M` has a cyclic vector (ii ⟹ i), so its centralizer is
  exactly `K[M]` (i ⟹ iii); and `dim_K K[M] = deg(minpoly K M) = deg(charpoly M)
  = n`.  This is the equality case of the Frobenius bound `dim_K C(M) ≥ n`: the
  commutant of a nonderogatory matrix is as small as it can possibly be.

  All results are `0`-sorry / `0`-axiom on top of Mathlib and the sibling files.
-/
import Mathlib
import Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ02OQ01

open Matrix Polynomial

noncomputable section

namespace CyclicCommutantDimension

open GeneralCyclicVector

variable {K : Type*} [Field K] {n : ℕ}

/-! ### The forward edge (ii) ⟹ (iii): nonderogatory ⟹ `C(M) = K[M]` -/

/-- **Forward edge of the triple equivalence (ii) ⟹ (iii).**  If `M` is
    nonderogatory (`minpoly K M = charpoly M`), then its centralizer coincides
    with the algebra of polynomials in `M`:

      `C(M) = {N : NM = MN} = Algebra.adjoin K {M} = K[M]`.

    The inclusion `K[M] ⊆ C(M)` is automatic (polynomials in `M` commute with
    `M`).  For `C(M) ⊆ K[M]`: nonderogatory `M` has a cyclic vector (parent
    biconditional), and `commuting_matrix_is_polynomial` then writes every matrix
    commuting with `M` as a polynomial in `M`. -/
theorem centralizer_eq_adjoin_of_nonderogatory
    (M : Matrix (Fin n) (Fin n) K) (hM : minpoly K M = M.charpoly) :
    Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))
      = Algebra.adjoin K ({M} : Set (Matrix (Fin n) (Fin n) K)) := by
  -- nonderogatory ⟹ cyclic vector
  obtain ⟨v, hcyc⟩ :=
    (CyclicVectorBiconditional.nonderogatory_iff_has_cyclic_vector M).mp hM
  apply le_antisymm
  · -- `C(M) ⊆ K[M]`: a commuting matrix is a polynomial in `M`.
    intro A hA
    rw [Subalgebra.mem_centralizer_iff] at hA
    have hcomm : A * M = M * A := (hA M (by simp)).symm
    obtain ⟨p, rfl⟩ :=
      CyclicCommutant.commuting_matrix_is_polynomial M v hcyc A hcomm
    rw [Algebra.adjoin_singleton_eq_range_aeval K M]
    exact ⟨p, rfl⟩
  · -- `K[M] ⊆ C(M)`: `M` commutes with `M`, so `adjoin K {M}` centralizes `M`.
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rfl

/-! ### The full (ii) ⟺ (iii) biconditional -/

/-- **Commutant characterization of nonderogatory matrices.**  The centralizer of
    `M` equals `K[M]` **iff** `M` is nonderogatory.  This packages the new
    forward edge with the sibling converse
    `centralizer_eq_adjoin_implies_nonderogatory`, closing the (ii) ⟺ (iii) edge
    of the triple equivalence. -/
theorem centralizer_eq_adjoin_iff_nonderogatory
    (M : Matrix (Fin n) (Fin n) K) :
    Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))
        = Algebra.adjoin K ({M} : Set (Matrix (Fin n) (Fin n) K))
      ↔ minpoly K M = M.charpoly :=
  ⟨CyclicCommutantConverse.centralizer_eq_adjoin_implies_nonderogatory M,
   centralizer_eq_adjoin_of_nonderogatory M⟩

/-! ### The headline: `dim_K C(M) = n` -/

/-- **Commutant dimension (headline).**  For a nonderogatory `n × n` matrix `M`
    over a field `K`, the centralizer `C(M) = {N : NM = MN}` has `K`-dimension
    exactly `n`:

      `dim_K C(M) = n`.

    This is the equality case of the Frobenius bound `dim_K C(M) ≥ n`
    (`finrank_centralizer_ge`): among all `n × n` matrices, the nonderogatory
    ones are precisely those whose commutant is as small as possible.

    Proof: `C(M) = K[M]` (forward edge) and
    `dim_K K[M] = deg(minpoly K M) = deg(charpoly M) = n`. -/
theorem finrank_centralizer_eq_of_nonderogatory
    (M : Matrix (Fin n) (Fin n) K) (hM : minpoly K M = M.charpoly) :
    Module.finrank K
        ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))) = n := by
  rw [centralizer_eq_adjoin_of_nonderogatory M hM,
    CyclicCommutantConverse.finrank_adjoin_eq_natDegree_minpoly M, hM,
    M.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- The commutant dimension equals `deg(charpoly M)` for nonderogatory `M`
    (a restatement of the headline before collapsing `deg(charpoly) = n`). -/
theorem finrank_centralizer_eq_natDegree_charpoly
    (M : Matrix (Fin n) (Fin n) K) (hM : minpoly K M = M.charpoly) :
    Module.finrank K
        ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)))
      = M.charpoly.natDegree := by
  rw [finrank_centralizer_eq_of_nonderogatory M hM, M.charpoly_natDegree_eq_dim,
    Fintype.card_fin]

/-- **Commutant dimension from `C(M) = K[M]`.**  If the centralizer of `M` already
    coincides with the polynomial algebra `K[M]`, then it has `K`-dimension exactly
    `n`.  This is the `(iii) ⟹ dim = n` edge: together with `(ii) ⟹ (iii)`
    (`centralizer_eq_adjoin_of_nonderogatory`) and `(ii) ⟹ dim = n`
    (`finrank_centralizer_eq_of_nonderogatory`) it names all three forward
    implications among {nonderogatory, `C(M) = K[M]`, `dim = n`} that are available
    without the Frobenius invariant-factor formula.  Obtained by feeding the
    characterization `centralizer_eq_adjoin_iff_nonderogatory` into the headline. -/
theorem finrank_centralizer_eq_of_centralizer_eq_adjoin
    (M : Matrix (Fin n) (Fin n) K)
    (h : Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))
        = Algebra.adjoin K ({M} : Set (Matrix (Fin n) (Fin n) K))) :
    Module.finrank K
        ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))) = n :=
  finrank_centralizer_eq_of_nonderogatory M
    ((centralizer_eq_adjoin_iff_nonderogatory M).mp h)

/-! ### A dimensional criterion for `C(M) = K[M]` -/

/-- `K[M] ⊆ C(M)` always: polynomials in `M` commute with `M`.  (The easy half of
    the (ii) ⟹ (iii) inclusion, isolated here for the dimensional argument.) -/
theorem adjoin_le_centralizer
    (M : Matrix (Fin n) (Fin n) K) :
    Algebra.adjoin K ({M} : Set (Matrix (Fin n) (Fin n) K))
      ≤ Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)) := by
  apply Algebra.adjoin_le
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  rfl

/-- **Dimensional criterion for the commutant.**  Since `K[M] ⊆ C(M)` always holds
    and `dim_K K[M] = deg(minpoly K M)`, the centralizer coincides with the
    polynomial algebra **iff** its dimension is no larger than it has to be:

      `C(M) = K[M]  ⟺  dim_K C(M) = deg(minpoly K M)`.

    The forward direction is immediate.  For the converse, `K[M] ⊆ C(M)` are nested
    subspaces of the finite-dimensional matrix algebra with equal `K`-dimension, so
    they coincide (`Submodule.eq_of_le_of_finrank_eq`).  This is the "no room above
    the polynomials" test: the commutant is exactly `K[M]` precisely when it does
    not grow past `deg(minpoly K M)`. -/
theorem centralizer_eq_adjoin_iff_finrank_eq_natDegree_minpoly
    (M : Matrix (Fin n) (Fin n) K) :
    Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))
        = Algebra.adjoin K ({M} : Set (Matrix (Fin n) (Fin n) K))
      ↔ Module.finrank K
          ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)))
        = (minpoly K M).natDegree := by
  constructor
  · intro h
    rw [h]
    exact CyclicCommutantConverse.finrank_adjoin_eq_natDegree_minpoly M
  · intro hf
    -- `K[M] ⊆ C(M)` as submodules, with equal finrank, hence equal.
    have hlesub :
        (Algebra.adjoin K ({M} : Set (Matrix (Fin n) (Fin n) K))).toSubmodule
          ≤ (Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))).toSubmodule := by
      intro x hx
      rw [Subalgebra.mem_toSubmodule] at hx ⊢
      exact adjoin_le_centralizer M hx
    have hfeq :
        Module.finrank K
            (Algebra.adjoin K ({M} : Set (Matrix (Fin n) (Fin n) K))).toSubmodule
          = Module.finrank K
            (Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))).toSubmodule := by
      rw [Subalgebra.finrank_toSubmodule, Subalgebra.finrank_toSubmodule,
        CyclicCommutantConverse.finrank_adjoin_eq_natDegree_minpoly M, hf]
    exact (Subalgebra.toSubmodule_injective
      (Submodule.eq_of_le_of_finrank_eq hlesub hfeq)).symm

/-- **Commutant dimension as a nonderogatory test.**  Chaining the dimensional
    criterion with the commutant characterization
    `centralizer_eq_adjoin_iff_nonderogatory`, the centralizer of `M` has dimension
    exactly `deg(minpoly K M)` **iff** `M` is nonderogatory:

      `dim_K C(M) = deg(minpoly K M)  ⟺  minpoly K M = charpoly M`.

    (For a nonderogatory `M` this reads `dim_K C(M) = n`, the headline; for a
    derogatory `M` the strict Frobenius bound `dim_K C(M) > deg(minpoly K M)`
    fails this equality.) -/
theorem finrank_centralizer_eq_natDegree_minpoly_iff_nonderogatory
    (M : Matrix (Fin n) (Fin n) K) :
    Module.finrank K
        ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)))
        = (minpoly K M).natDegree
      ↔ minpoly K M = M.charpoly :=
  (centralizer_eq_adjoin_iff_finrank_eq_natDegree_minpoly M).symm.trans
    (centralizer_eq_adjoin_iff_nonderogatory M)

/-- **The always-true commutant lower bound** `deg(minpoly K M) ≤ dim_K C(M)`.  Since
    `K[M] ⊆ C(M)` (`adjoin_le_centralizer`) as `K`-submodules and `dim_K K[M] =
    deg(minpoly K M)` (`finrank_adjoin_eq_natDegree_minpoly`), `Submodule.finrank_mono`
    gives the inequality for *every* `M` — derogatory or not.  This is the elementary
    lower half of the Frobenius commutant bound; equality `dim_K C(M) = deg(minpoly K M)`
    is the nonderogatory case (`finrank_centralizer_eq_natDegree_minpoly_iff_nonderogatory`),
    while the file's other bound `dim_K C(M) ≥ n` (Frobenius) is the sharper form available
    only through the invariant-factor formula. -/
theorem natDegree_minpoly_le_finrank_centralizer
    (M : Matrix (Fin n) (Fin n) K) :
    (minpoly K M).natDegree
      ≤ Module.finrank K
          ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))) := by
  have hlesub :
      (Algebra.adjoin K ({M} : Set (Matrix (Fin n) (Fin n) K))).toSubmodule
        ≤ (Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))).toSubmodule := by
    intro x hx
    rw [Subalgebra.mem_toSubmodule] at hx ⊢
    exact adjoin_le_centralizer M hx
  have hmono := Submodule.finrank_mono hlesub
  rwa [Subalgebra.finrank_toSubmodule, Subalgebra.finrank_toSubmodule,
    CyclicCommutantConverse.finrank_adjoin_eq_natDegree_minpoly M] at hmono

/-! ### Summary -/

/-- **De Moivre / Cayley–Hamilton OQ-02-OQ-02 summary.**  For an `n × n` matrix
    `M` over a field `K`:

    (1) `C(M) = K[M]` ⟺ `M` is nonderogatory (`minpoly = charpoly`); and

    (2) when `M` is nonderogatory, `dim_K C(M) = n` — the equality case of the
        Frobenius bound `dim_K C(M) ≥ n`. -/
theorem cayley_hamilton_oq02_oq02_summary
    (M : Matrix (Fin n) (Fin n) K) :
    (Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))
        = Algebra.adjoin K ({M} : Set (Matrix (Fin n) (Fin n) K))
      ↔ minpoly K M = M.charpoly)
    ∧ (minpoly K M = M.charpoly →
        Module.finrank K
          ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))) = n) :=
  ⟨centralizer_eq_adjoin_iff_nonderogatory M,
   finrank_centralizer_eq_of_nonderogatory M⟩

end CyclicCommutantDimension

end
