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

/-- **Strict commutant lower bound for derogatory matrices.**  The always-true bound
    `deg(minpoly K M) ≤ dim_K C(M)` (`natDegree_minpoly_le_finrank_centralizer`) is an
    *equality* exactly for nonderogatory `M`
    (`finrank_centralizer_eq_natDegree_minpoly_iff_nonderogatory`).  Hence for a **derogatory**
    `M` (`minpoly K M ≠ charpoly M`) the inequality is **strict**:

      `deg(minpoly K M) < dim_K C(M)`.

    Equivalently, the commutant of a derogatory matrix is strictly larger than its polynomial
    algebra `K[M]`: it contains a matrix commuting with `M` that is *not* a polynomial in `M`.
    This is the dimensional signature of derogatoriness, dual to the nonderogatory equality
    case `dim_K C(M) = deg(minpoly K M) = n`. -/
theorem natDegree_minpoly_lt_finrank_centralizer_of_derogatory
    (M : Matrix (Fin n) (Fin n) K) (hM : minpoly K M ≠ M.charpoly) :
    (minpoly K M).natDegree
      < Module.finrank K
          ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))) := by
  have hle := natDegree_minpoly_le_finrank_centralizer M
  have hne :
      Module.finrank K
          ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)))
        ≠ (minpoly K M).natDegree := by
    intro heq
    exact hM ((finrank_centralizer_eq_natDegree_minpoly_iff_nonderogatory M).mp heq)
  omega

/-- **Dimensional dichotomy of the commutant.**  For every `n × n` matrix `M` the polynomial
    algebra `K[M]` sits inside the commutant `C(M)`, and the gap between their dimensions
    detects derogatoriness exactly:

      `dim_K C(M) = deg(minpoly K M)`  if `M` is nonderogatory, and
      `dim_K C(M) > deg(minpoly K M)`  if `M` is derogatory.

    Packages `finrank_centralizer_eq_natDegree_minpoly_iff_nonderogatory` (the equality case)
    with `natDegree_minpoly_lt_finrank_centralizer_of_derogatory` (the strict case) into a
    single case split on `minpoly K M = charpoly M`. -/
theorem finrank_centralizer_dichotomy
    (M : Matrix (Fin n) (Fin n) K) :
    (minpoly K M = M.charpoly →
        Module.finrank K
          ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)))
          = (minpoly K M).natDegree)
    ∧ (minpoly K M ≠ M.charpoly →
        (minpoly K M).natDegree
          < Module.finrank K
              ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)))) :=
  ⟨fun h => (finrank_centralizer_eq_natDegree_minpoly_iff_nonderogatory M).mpr h,
   natDegree_minpoly_lt_finrank_centralizer_of_derogatory M⟩

/-! ### The ambient-dimension (`= n`) reading of the converse -/

/-- **Nonderogatory ⟺ the minimal polynomial has full degree `n`.**  A matrix is
    nonderogatory (`minpoly K M = charpoly M`) **iff** its minimal polynomial already attains
    the maximal possible degree `n = Fintype.card (Fin n)`.  Since `minpoly K M ∣ charpoly M`
    are monic with `deg (charpoly M) = n` (`Matrix.charpoly_natDegree_eq_dim`), equality of the
    two polynomials is equivalent to equality of their degrees
    (`Polynomial.eq_of_monic_of_dvd_of_natDegree_le`).  This is the scalar (degree-level)
    characterization of nonderogatoriness, complementing the centralizer-dimension criteria:
    it is the hypothesis that the headline `finrank_centralizer_eq_of_nonderogatory`
    (`dim_K C(M) = n`) consumes. -/
theorem nonderogatory_iff_natDegree_minpoly_eq_dim
    (M : Matrix (Fin n) (Fin n) K) :
    minpoly K M = M.charpoly ↔ (minpoly K M).natDegree = Fintype.card (Fin n) := by
  constructor
  · intro h; rw [h, M.charpoly_natDegree_eq_dim]
  · intro hdeg
    have hM : IsIntegral K M := IsIntegral.of_finite K M
    have hdvd : minpoly K M ∣ M.charpoly := minpoly.dvd K M (Matrix.aeval_self_charpoly M)
    have hmin_monic : (minpoly K M).Monic := minpoly.monic hM
    have hdeg' : M.charpoly.natDegree ≤ (minpoly K M).natDegree := by
      rw [M.charpoly_natDegree_eq_dim, hdeg]
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmin_monic M.charpoly_monic hdvd
      hdeg').symm

/-- **The `= n` converse is exactly the sharp Frobenius bound.**  The headline
    `finrank_centralizer_eq_of_nonderogatory` proves the forward implication
    `nonderogatory M → dim_K C(M) = n`.  Its converse `dim_K C(M) = n → nonderogatory M`
    is *not* derivable from the elementary bounds in this file: `finrank_centralizer_ge`
    (`n ≤ dim_K C(M)`) together with the strict derogatory bound
    `natDegree_minpoly_lt_finrank_centralizer_of_derogatory` (`deg(minpoly) < dim_K C(M)`)
    only give `n ≤ dim_K C(M)` — never a *strict* `n < dim_K C(M)` for derogatory `M`, since
    `deg(minpoly) < n` there.  The precise missing input is the **sharp Frobenius strictness**:
    every derogatory matrix has `n < dim_K C(M)` (the invariant-factor content of Frobenius'
    formula `dim_K C(M) = Σ (2i-1) deg dᵢ`, with `≥ 2` invariant factors forcing a strict
    excess), which is not yet formalized in this chain.

    This lemma records that reduction honestly: **assuming** the sharp strictness hypothesis,
    `dim_K C(M) = n` forces `M` nonderogatory.  Discharging `hsharp` unconditionally is the
    sole remaining gap between the forward headline and a full `dim_K C(M) = n ⟺ nonderogatory`
    biconditional at the ambient dimension. -/
theorem nonderogatory_of_finrank_centralizer_eq_dim
    (hsharp : ∀ M : Matrix (Fin n) (Fin n) K, minpoly K M ≠ M.charpoly →
        Fintype.card (Fin n) < Module.finrank K
          ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))))
    (M : Matrix (Fin n) (Fin n) K)
    (h : Module.finrank K
        ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)))
        = Fintype.card (Fin n)) :
    minpoly K M = M.charpoly := by
  by_contra hderog
  have hlt := hsharp M hderog
  omega

/-! ### Elementwise (matrix-level) forms -/

/-- **Elementwise commutant characterization for nonderogatory `M`.**  All the results
    above are phrased at the level of the subalgebra `C(M) = Subalgebra.centralizer …`.
    Unfolded to individual matrices, for a nonderogatory `M` a matrix `N` commutes with
    `M` **iff** it is a polynomial in `M`:

      `N * M = M * N  ⟺  ∃ p, aeval M p = N`.

    This is the pointwise reading of `centralizer_eq_adjoin_of_nonderogatory`
    (`C(M) = K[M]`) via `Algebra.adjoin_singleton_eq_range_aeval`: the directly usable
    "commuting = polynomial" form of the (i) ⟹ (iii) edge. -/
theorem commute_iff_mem_range_aeval_of_nonderogatory
    (M : Matrix (Fin n) (Fin n) K) (hM : minpoly K M = M.charpoly)
    (N : Matrix (Fin n) (Fin n) K) :
    N * M = M * N ↔ ∃ p : K[X], (aeval M) p = N := by
  constructor
  · intro hcomm
    have hN : N ∈ Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg; rw [Set.mem_singleton_iff] at hg; subst hg
      exact hcomm.symm
    rw [centralizer_eq_adjoin_of_nonderogatory M hM,
      Algebra.adjoin_singleton_eq_range_aeval] at hN
    exact hN
  · rintro ⟨p, rfl⟩
    have hmem : (aeval M) p ∈ Algebra.adjoin K ({M} : Set (Matrix (Fin n) (Fin n) K)) := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨p, rfl⟩
    have hc := adjoin_le_centralizer M hmem
    rw [Subalgebra.mem_centralizer_iff] at hc
    exact (hc M (Set.mem_singleton M)).symm

/-- **A derogatory matrix has a commuting non-polynomial — formalized.**  The strict bound
    `natDegree_minpoly_lt_finrank_centralizer_of_derogatory` says a derogatory commutant is
    strictly larger than `K[M]`; its docstring reads "it contains a matrix commuting with `M`
    that is not a polynomial in `M`".  Here that existential is made explicit and turned into
    an iff:

      `(∃ N, N·M = M·N ∧ N ∉ K[M])  ⟺  M is derogatory (minpoly ≠ charpoly)`.

    Forward: such an `N` witnesses `C(M) ≠ K[M]`, so by
    `centralizer_eq_adjoin_iff_nonderogatory` `M` is not nonderogatory.  Backward:
    derogatoriness gives `K[M] < C(M)` (proper, via `adjoin_le_centralizer`), and
    `SetLike.exists_of_lt` extracts a commuting matrix outside `K[M]`. -/
theorem exists_commute_not_mem_adjoin_iff_derogatory
    (M : Matrix (Fin n) (Fin n) K) :
    (∃ N : Matrix (Fin n) (Fin n) K, N * M = M * N ∧
        N ∉ Algebra.adjoin K ({M} : Set (Matrix (Fin n) (Fin n) K)))
      ↔ minpoly K M ≠ M.charpoly := by
  constructor
  · rintro ⟨N, hcomm, hnotmem⟩ hnon
    have hN : N ∈ Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)) := by
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg; rw [Set.mem_singleton_iff] at hg; subst hg
      exact hcomm.symm
    rw [centralizer_eq_adjoin_of_nonderogatory M hnon] at hN
    exact hnotmem hN
  · intro hderog
    have hne : Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))
        ≠ Algebra.adjoin K ({M} : Set (Matrix (Fin n) (Fin n) K)) :=
      fun heq => hderog ((centralizer_eq_adjoin_iff_nonderogatory M).mp heq)
    have hlt : Algebra.adjoin K ({M} : Set (Matrix (Fin n) (Fin n) K))
        < Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)) :=
      lt_of_le_of_ne (adjoin_le_centralizer M) (Ne.symm hne)
    obtain ⟨N, hNc, hNa⟩ := SetLike.exists_of_lt hlt
    refine ⟨N, ?_, hNa⟩
    rw [Subalgebra.mem_centralizer_iff] at hNc
    exact (hNc M (Set.mem_singleton M)).symm

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

/-! ### The commutant of a nonderogatory matrix is abelian

For a nonderogatory `M` the centralizer is `C(M) = K[M]` (`centralizer_eq_adjoin_of_nonderogatory`),
and polynomials in a single matrix commute with one another.  So *any two* matrices that each
commute with `M` automatically commute with *each other*: the commutant is a commutative algebra.
This is a distinctive feature of the nonderogatory case — for a derogatory `M` the commutant is
strictly larger than `K[M]` and generally non-abelian. -/

/-- **Commuting matrices with a nonderogatory `M` pairwise commute.**  If `M` is nonderogatory
    (`minpoly K M = charpoly M`) and both `N₁` and `N₂` commute with `M`, then `N₁` and `N₂`
    commute with each other: `N₁ N₂ = N₂ N₁`.  Since each `Nᵢ` is a polynomial in `M`
    (`commute_iff_mem_range_aeval_of_nonderogatory`), write `Nᵢ = p_i(M)`; then
    `p_1(M) p_2(M) = (p_1 p_2)(M) = (p_2 p_1)(M) = p_2(M) p_1(M)` by `map_mul` and the
    commutativity of `K[X]`. -/
theorem commute_of_commute_nonderogatory
    (M : Matrix (Fin n) (Fin n) K) (hM : minpoly K M = M.charpoly)
    (N₁ N₂ : Matrix (Fin n) (Fin n) K)
    (h₁ : N₁ * M = M * N₁) (h₂ : N₂ * M = M * N₂) :
    N₁ * N₂ = N₂ * N₁ := by
  obtain ⟨p, rfl⟩ := (commute_iff_mem_range_aeval_of_nonderogatory M hM N₁).mp h₁
  obtain ⟨q, rfl⟩ := (commute_iff_mem_range_aeval_of_nonderogatory M hM N₂).mp h₂
  rw [← map_mul, ← map_mul, mul_comm p q]

/-- **The commutant of a nonderogatory matrix is abelian (subalgebra form).**  Any two elements
    `A, B` of the centralizer `C(M)` of a nonderogatory `M` commute: `A B = B A`.  This is the
    subalgebra-level reading of `commute_of_commute_nonderogatory` — `C(M) = K[M]` is a
    commutative algebra — obtained by unfolding centralizer membership to the commuting relations
    with `M`.  (No `CommRing` instance on the subalgebra is needed.) -/
theorem centralizer_mul_comm_of_nonderogatory
    (M : Matrix (Fin n) (Fin n) K) (hM : minpoly K M = M.charpoly)
    (A B : Matrix (Fin n) (Fin n) K)
    (hA : A ∈ Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)))
    (hB : B ∈ Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))) :
    A * B = B * A := by
  rw [Subalgebra.mem_centralizer_iff] at hA hB
  exact commute_of_commute_nonderogatory M hM A B
    (hA M (Set.mem_singleton M)).symm (hB M (Set.mem_singleton M)).symm

end CyclicCommutantDimension

end
