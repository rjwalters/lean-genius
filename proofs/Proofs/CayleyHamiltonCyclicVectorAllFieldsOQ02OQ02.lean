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
    rw [Algebra.adjoin_singleton_eq_range_aeval]
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
