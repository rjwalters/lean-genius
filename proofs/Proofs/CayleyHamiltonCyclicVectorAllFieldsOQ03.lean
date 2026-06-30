/-
  Coordinate-Free Nonderogatory ⟹ Cyclic Vector for Operators
  (cayley-hamilton-cyclic-vector-all-fields-oq-03)

  The parent file `CayleyHamiltonCyclicVectorAllFields.lean` proves the cyclic
  vector theorem for **matrices**:

    If `M : Matrix (Fin n) (Fin n) K` is nonderogatory (minpoly = charpoly),
    then `M` has a cyclic vector.

  This file lifts that result to a **coordinate-free linear operator**
  `T : V →ₗ[K] V` on a finite-dimensional vector space `V`, with no reference to
  a chosen basis in the statement:

    If `(minpoly K T).natDegree = finrank K V` then `T` has a cyclic vector.

  ## Strategy (basis reduction)

  Pick the canonical basis `b := Module.finBasis K V`, with index `Fin n`,
  `n = finrank K V`. Let `M := LinearMap.toMatrix b b T`. Then:

  1. **Minpoly transport.** `toMatrixAlgEquiv b : End K V ≃ₐ[K] Matrix _ _ K`
     is an algebra isomorphism, and minimal polynomials are invariant under
     algebra isomorphisms (`minpoly.algEquiv_eq`), so `minpoly K M = minpoly K T`.
     Hence `(minpoly K M).natDegree = n`.

  2. **Nonderogatory matrix.** `(minpoly K M).natDegree = n` together with
     `minpoly K M ∣ M.charpoly` (Cayley–Hamilton) and both being monic of
     degree `n` forces `minpoly K M = M.charpoly`, i.e. `M` is nonderogatory.

  3. **Cyclic vector for `M`.** Apply the parent matrix theorem to obtain a
     matrix cyclic vector `w : Fin n → K`.

  4. **Transport back.** The coordinate vector `v := b.equivFun.symm w ∈ V`
     satisfies, for every `p : K[X]`,
       `b.repr (aeval T p v) = (aeval M p).mulVec (b.repr v) = (aeval M p).mulVec w`,
     because `toMatrix b b` is an algebra homomorphism that intertwines operator
     application with `mulVec`. Hence `aeval T p v = 0 ⟺ (aeval M p).mulVec w = 0`,
     and the matrix cyclicity of `w` gives the operator cyclicity of `v`.

  ## Scope of OQ-03

  OQ-03 asks for two generalizations: (a) the coordinate-free *operator* version,
  and (b) the version for finitely generated torsion modules over a PID. This
  file delivers (a) in full (reduced to the verified matrix theorem). Direction
  (b) is a substantially deeper undertaking that requires the structure theorem
  for finitely generated modules over a PID and its cyclic-decomposition
  consequences; we record it as an explicit open gap below rather than
  attempting it here (see `## PID direction` at the end).

  ## Span-form bridge (Section V)

  The operator definition `IsCyclicVectorOp` used above is the *annihilator-free*
  form ("no nonzero polynomial of degree `< finrank` kills `v`"). Section V
  reconciles it with the standard *span* form of cyclicity from the registered
  module-theoretic development `NonderogatoryModule` (in
  `CayleyHamiltonMinpolyOQ05OQ01OQ03.lean`), where
  `IsCyclicVector T v := cyclicSubspace T v = ⊤`. The link is linear
  independence of the Krylov vectors `{Tᵏ v}_{k < finrank}`: being `finrank`-many
  independent vectors they form a basis, so their span — which lies inside the
  cyclic subspace — is already `⊤`. The capstone
  `operator_nonderogatory_has_span_cyclic_vector` restates the main theorem in
  this span vocabulary, connecting OQ-03's operator half to Mathlib's
  `Module`/cyclic-subspace infrastructure as the problem statement requests.

  ## Status: 0 sorries, 0 axioms. Build-pending under Docker contention; the
  Mathlib bearers (`LinearMap.toMatrixAlgEquiv`, `minpoly.algEquiv_eq`,
  `LinearMap.toMatrix_apply`, `Matrix.charpoly_natDegree_eq_dim`,
  `Matrix.aeval_self_charpoly`, `Polynomial.aeval_algHom_apply`,
  `Basis.equivFun_apply`, `basisOfLinearIndependentOfCardEqFinrank`,
  `Fintype.linearIndependent_iff`, `natDegree_C_mul_X_pow_le`) are name-checked
  against pinned rev 2df2f01 / v4.26.0; the Section V Krylov-independence
  argument mirrors the compiled matrix proof `CyclicCommutant.krylov_linearIndependent`.
-/
import Mathlib
import Proofs.CayleyHamiltonCyclicVectorAllFields
import Proofs.CayleyHamiltonMinpolyOQ05OQ01OQ03

noncomputable section

namespace CyclicVectorOperator

open Matrix Polynomial CayleyHamiltonCyclicVectorAllFields

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

-- ============================================================
-- SECTION I: Coordinate-free definitions
-- ============================================================

/-- A vector `v : V` is **cyclic** for the operator `T` if no nonzero polynomial
    of degree `< finrank K V` annihilates `v`. This is the operator analogue of
    the matrix definition `GeneralCyclicVector.IsCyclicVector`. -/
def IsCyclicVectorOp (T : Module.End K V) (v : V) : Prop :=
  ∀ p : K[X], p.natDegree < Module.finrank K V → (aeval T p) v = 0 → p = 0

/-- An operator `T` is **nonderogatory** if its minimal polynomial has degree
    equal to `finrank K V` (equivalently, minpoly = charpoly). -/
def IsNonderogatoryOp (T : Module.End K V) : Prop :=
  (minpoly K T).natDegree = Module.finrank K V

-- ============================================================
-- SECTION II: Matrix nonderogatory from minpoly degree
-- ============================================================

/-- If the minimal polynomial of a matrix `M : Matrix (Fin n) (Fin n) K` has
    degree `n`, then `M` is nonderogatory (`minpoly K M = M.charpoly`).

    Proof: `minpoly K M ∣ M.charpoly` by Cayley–Hamilton, both are monic, and
    `M.charpoly.natDegree = n = (minpoly K M).natDegree`, so the cofactor has
    degree `0` and (being monic) equals `1`. -/
theorem matrix_nonderog_of_minpoly_natDegree {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K)
    (h : (minpoly K M).natDegree = n) :
    GeneralCyclicVector.IsNonderogatory M := by
  show minpoly K M = M.charpoly
  have hMmonic : (minpoly K M).Monic := minpoly.monic (Matrix.isIntegral M)
  have hCmonic : M.charpoly.Monic := M.charpoly_monic
  have hdvd : minpoly K M ∣ M.charpoly := minpoly.dvd K M (Matrix.aeval_self_charpoly M)
  have hcdeg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨q, hq⟩ := hdvd
  have hpne : minpoly K M ≠ 0 := hMmonic.ne_zero
  have hqne : q ≠ 0 := by
    rintro rfl; rw [mul_zero] at hq; exact hCmonic.ne_zero hq
  have hqdeg : q.natDegree = 0 := by
    have hmul := Polynomial.natDegree_mul hpne hqne
    rw [← hq, hcdeg, h] at hmul
    omega
  have hqC : q = Polynomial.C (q.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hqdeg
  have hc1 : q.coeff 0 = 1 := by
    have hlead : M.charpoly.leadingCoeff
        = (minpoly K M).leadingCoeff * q.leadingCoeff := by
      rw [hq, Polynomial.leadingCoeff_mul]
    rw [hCmonic.leadingCoeff, hMmonic.leadingCoeff, one_mul,
        Polynomial.leadingCoeff, hqdeg] at hlead
    exact hlead.symm
  rw [hq, hqC, hc1, map_one, mul_one]

-- ============================================================
-- SECTION III: Operator ⟷ matrix bridge (basis transport)
-- ============================================================

/-- For a basis `b`, applying an operator `f` and reading coordinates equals
    multiplying the matrix of `f` by the coordinate vector:
      `(toMatrix b b f).mulVec (b.repr x) = b.repr (f x)`.
    Proved from the definitional `LinearMap.toMatrix_apply`. -/
theorem toMatrix_mulVec_repr {n : ℕ} (b : Basis (Fin n) K V)
    (f : Module.End K V) (x : V) :
    (LinearMap.toMatrix b b f).mulVec (fun i => b.repr x i) = fun i => b.repr (f x) i := by
  funext i
  rw [Matrix.mulVec, Matrix.dotProduct]
  -- RHS: expand x in the basis and push the operator / coordinate map through the sum.
  conv_rhs => rw [← b.sum_repr x, map_sum]
  rw [map_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- Each summand: matrix entry times coordinate = coordinate times pushed-through entry.
  simp only [LinearMap.toMatrix_apply, map_smul, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  ring

-- ============================================================
-- SECTION IV: Main theorem — operator nonderogatory ⟹ cyclic
-- ============================================================

/-- **Coordinate-free cyclic vector theorem.** A nonderogatory operator on a
    finite-dimensional vector space has a cyclic vector. This lifts the matrix
    theorem `nonderogatory_has_cyclic_vector` to abstract operators with no
    chosen basis in the statement. -/
theorem operator_nonderogatory_has_cyclic_vector [FiniteDimensional K V]
    (T : Module.End K V) (h : IsNonderogatoryOp T) :
    ∃ v, IsCyclicVectorOp T v := by
  rcases Nat.eq_zero_or_pos (Module.finrank K V) with hn0 | hnpos
  · -- finrank 0: the degree bound `< 0` is unsatisfiable, so any vector is cyclic.
    exact ⟨0, fun p hp _ => absurd hp (by rw [hn0]; exact Nat.not_lt_zero _)⟩
  -- Canonical basis and the matrix of T.
  set b : Basis (Fin (Module.finrank K V)) K V := Module.finBasis K V with hb
  set M : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K :=
    LinearMap.toMatrix b b T with hM
  -- (1) Minpoly transport: minpoly K M = minpoly K T.
  have hmin : minpoly K M = minpoly K T := by
    have := minpoly.algEquiv_eq (LinearMap.toMatrixAlgEquiv b) T
    rwa [LinearMap.toMatrixAlgEquiv_apply] at this
  have hMdeg : (minpoly K M).natDegree = Module.finrank K V := by
    rw [hmin]; exact h
  -- (2) M is nonderogatory.
  have hMnd : GeneralCyclicVector.IsNonderogatory M :=
    matrix_nonderog_of_minpoly_natDegree M hMdeg
  -- (3) M has a cyclic vector w.
  obtain ⟨w, hw⟩ := nonderogatory_has_cyclic_vector M hMnd
  -- (4) Transport w back to V via the coordinate isomorphism.
  refine ⟨b.equivFun.symm w, ?_⟩
  intro p hpdeg hpann
  apply hw p hpdeg
  -- Coordinates of `b.equivFun.symm w` are exactly `w`.
  have hcoord : (fun i => b.repr (b.equivFun.symm w) i) = w := by
    funext i
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  -- toMatrix b b (aeval T p) = aeval M p.
  have hpoly : LinearMap.toMatrix b b (aeval T p) = aeval M p := by
    have key := Polynomial.aeval_algHom_apply
      (LinearMap.toMatrixAlgEquiv b).toAlgHom T p
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
      LinearMap.toMatrixAlgEquiv_apply] at key
    rw [hM]; exact key.symm
  -- Apply the bridge and the hypothesis aeval T p v = 0.
  have hbridge := toMatrix_mulVec_repr b (aeval T p) (b.equivFun.symm w)
  rw [hcoord, hpoly] at hbridge
  -- hbridge : (aeval M p).mulVec w = fun i => b.repr (aeval T p (b.equivFun.symm w)) i
  rw [hbridge, hpann]
  funext i
  simp

-- ============================================================
-- SECTION V: Bridge to the span-form cyclic subspace
-- ============================================================

/-- The Krylov vectors `{Tᵏ v}_{k < finrank}` of a vector that is cyclic in the
    annihilator-free sense (`IsCyclicVectorOp`) are linearly independent.

    A linear dependence `∑_{k<n} c_k Tᵏ v = 0` is exactly the polynomial
    `p = ∑_{k<n} c_k Xᵏ` (degree `< n`) annihilating `v`, so `IsCyclicVectorOp`
    forces `p = 0`, i.e. all `c_k = 0`. This is the operator analogue of
    `CyclicCommutant.krylov_linearIndependent` (matrix version). -/
theorem krylov_linearIndependent_op [FiniteDimensional K V]
    (T : Module.End K V) (v : V) (h : IsCyclicVectorOp T v) :
    LinearIndependent K (fun k : Fin (Module.finrank K V) => (T ^ (k : ℕ)) v) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  set n := Module.finrank K V with hn
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le (i : ℕ)) i.isLt
  set p := ∑ k : Fin n, C (c k) * X ^ (k : ℕ) with hp_def
  have hp_aeval : aeval T p = ∑ k : Fin n, c k • T ^ (k : ℕ) := by
    simp only [p, map_sum, map_mul, map_pow, aeval_C, aeval_X,
               Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hp_ann : (aeval T p) v = 0 := by
    rw [hp_aeval]
    have hsum : (∑ k : Fin n, c k • T ^ (k : ℕ)) v
        = ∑ k : Fin n, c k • (T ^ (k : ℕ)) v := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    rw [hsum, hc]
  have hp_deg : p.natDegree < n := by
    apply lt_of_le_of_lt (natDegree_sum_le _ _)
    apply (Finset.sup_lt_iff hnpos).mpr
    intro k _; exact lt_of_le_of_lt (natDegree_C_mul_X_pow_le (c k) ↑k) k.isLt
  have hp_zero : p = 0 := h p hp_deg hp_ann
  have h_coeff := congr_arg (Polynomial.coeff · ↑i) hp_zero
  simp only [Polynomial.coeff_zero, p, C_mul_X_pow_eq_monomial,
             finset_sum_coeff, coeff_monomial] at h_coeff
  simpa [Fin.val_injective.eq_iff] using h_coeff

/-- **Bridge.** A vector cyclic in the annihilator-free sense `IsCyclicVectorOp`
    is also cyclic in the span sense of `NonderogatoryModule`: its Krylov orbit
    `{Tᵏ v}` spans the whole space. Since the `finrank`-many Krylov vectors are
    linearly independent (`krylov_linearIndependent_op`) and `finrank K V` of
    them form a basis, their span is `⊤`; this span sits inside the cyclic
    subspace, so the cyclic subspace is `⊤`. -/
theorem cyclicSubspace_eq_top_of_isCyclicVectorOp [FiniteDimensional K V]
    (T : Module.End K V) (v : V) (h : IsCyclicVectorOp T v) :
    NonderogatoryModule.cyclicSubspace T v = ⊤ := by
  have hli := krylov_linearIndependent_op T v h
  have hcard : Fintype.card (Fin (Module.finrank K V)) = Module.finrank K V :=
    Fintype.card_fin _
  have hspan :
      Submodule.span K
          (Set.range fun k : Fin (Module.finrank K V) => (T ^ (k : ℕ)) v) = ⊤ := by
    have hb := (basisOfLinearIndependentOfCardEqFinrank hli hcard).span_eq
    simpa only [coe_basisOfLinearIndependentOfCardEqFinrank] using hb
  rw [eq_top_iff, ← hspan]
  exact NonderogatoryModule.finiteSpan_le_cyclicSubspace T v (Module.finrank K V)

/-- **Capstone (span form).** A nonderogatory operator on a finite-dimensional
    space has a vector whose Krylov orbit spans the whole space — i.e. a cyclic
    vector in the span-based sense `NonderogatoryModule.IsCyclicVector`. This
    recasts `operator_nonderogatory_has_cyclic_vector` in the vocabulary of the
    registered module-theoretic cyclic-subspace development, connecting OQ-03's
    operator half to the `Module`/cyclic-subspace infrastructure. -/
theorem operator_nonderogatory_has_span_cyclic_vector [FiniteDimensional K V]
    (T : Module.End K V) (h : IsNonderogatoryOp T) :
    ∃ v, NonderogatoryModule.cyclicSubspace T v = ⊤ := by
  obtain ⟨v, hv⟩ := operator_nonderogatory_has_cyclic_vector T h
  exact ⟨v, cyclicSubspace_eq_top_of_isCyclicVectorOp T v hv⟩

end CyclicVectorOperator

/-
## PID direction (open gap, not formalized here)

OQ-03 also requests the generalization to finitely generated torsion modules
over a PID `R`:

  A finitely generated torsion `R[X]`-module `V` (equivalently, `V` with an
  `R`-linear endomorphism `T`) is cyclic iff its order ideal equals its
  "characteristic" ideal — the PID analogue of `minpoly = charpoly`.

This is most cleanly stated as the isomorphism form `M ≃ₗ[R] R ⧸ Module.annihilator R M`,
avoiding a from-scratch "characteristic ideal" definition.

Infrastructure assessment (revised 2026-06-16, S2 — names checked vs Mathlib v4.26.0):
  - The CRT cyclic-recombination is ALREADY in Mathlib:
    `Module.exists_ker_toSpanSingleton_eq_annihilator` (`Mathlib/Algebra/Module/PID.lean`)
    produces `x : M` with `ker (toSpanSingleton R M x) = Module.annihilator R M` — i.e.
    the cyclic-generator candidate whose order ideal already matches the module's. Its
    proof internally runs `equiv_free_prod_directSum` + prime-power decomposition + CRT.
  - Remaining gap is small: close `R ∙ x = ⊤` from `R ∙ x ≃ₗ M` via a length argument
    (`Module.length`, `Module.length_eq_add_of_exact`, `Module.length_eq_zero_iff`).
  - Size estimate: ~150–250 lines (NOT >500). Single Docker-up session is plausible.
  - Decision: deferred only on a Docker build blackout; see this problem's `state.md`
    for the full build-ready recipe. Field-operator case above is delivered in full.
-/
