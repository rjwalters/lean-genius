/-
  Frobenius equality for a cyclic endomorphism: dim centralizer = dim V
  (cayley-hamilton-cyclic-vector-all-fields-oq-02-oq-03)

  This file sharpens the general Frobenius **lower** bound
  (`CyclicCommutantConverse.endK_centralizer_bound`:
   `dim_K V ≤ dim_K C(T)` for every `T : Module.End K V`) to an **equality**
  in the cyclic (nonderogatory) case, using the commutant characterization
  `EndCyclicCommutant.commuting_end_is_polynomial` established in
  `CayleyHamiltonCyclicVectorAllFieldsOQ02OQ03.lean`.

  ## Statement

  Let `V` be finite-dimensional and `T : Module.End K V` have a cyclic vector
  `v` (`IsEndCyclicVector`).  Then the centralizer `C(T) = {A | A·T = T·A}`
  inside `Module.End K V` has `K`-dimension **exactly** `dim_K V`:

      dim_K C(T) = dim_K V.

  This is the equality case of the Frobenius bound — the nonderogatory /
  minimal-centralizer edge of the triple equivalence
  `nonderogatory ⟺ cyclic ⟺ C(T) = K[T]`.

  ## Proof

  * `≥` is the general bound `endK_centralizer_bound`.
  * `≤` is the elegant half specific to a cyclic vector: **evaluation at `v`**,
    `A ↦ A·v`, is an injective `K`-linear map `C(T) → V`.  Injectivity is
    `commuting_end_eq_of_apply_eq`: two endomorphisms commuting with `T` that
    agree on the cyclic vector `v` agree on the whole Krylov basis
    `{Tᵏ·v}` — since `A·(Tᵏ·v) = Tᵏ·(A·v)` — hence are equal (`Basis.ext`).
    An injective linear map into `V` forces `dim C(T) ≤ dim V`.

  Status: 0 sorries, 0 axioms.
-/
import Mathlib
import Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ02OQ03
import Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ02OQ01

noncomputable section

namespace EndCyclicCommutant

open Polynomial Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

-- ============================================================
-- SECTION I: agreement on a cyclic vector forces operator equality
-- ============================================================

/-- **Rigidity on a cyclic vector.**  If `A` and `B` both commute with `T` and
    agree on a cyclic vector `v` (`A·v = B·v`), then `A = B`.  Two operators
    commuting with `T` are determined by their value at `v`, because they then
    agree on the whole Krylov basis `{Tᵏ·v}`:
    `A·(Tᵏ·v) = Tᵏ·(A·v) = Tᵏ·(B·v) = B·(Tᵏ·v)`.  This is the injectivity of
    the evaluation map `A ↦ A·v` on the centralizer. -/
theorem commuting_end_eq_of_apply_eq [FiniteDimensional K V]
    (T : Module.End K V) (v : V) (hcyc : IsEndCyclicVector T v)
    (A B : Module.End K V) (hA : A * T = T * A) (hB : B * T = T * B)
    (hAB : A v = B v) : A = B := by
  rcases Nat.eq_zero_or_pos (finrank K V) with h0 | hn
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    exact Subsingleton.elim _ _
  set n := finrank K V with hn_def
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hli : LinearIndependent K (fun k : Fin n => (T ^ (k : ℕ)) v) :=
    endKrylov_linearIndependent T v hcyc hn
  set b : Module.Basis (Fin n) K V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin]) with hb_def
  have hb : ∀ i, b i = (T ^ (i : ℕ)) v := by
    intro i; rw [hb_def, coe_basisOfLinearIndependentOfCardEqFinrank]
  apply b.ext
  intro i
  rw [hb i]
  have eA : A ((T ^ (i : ℕ)) v) = (T ^ (i : ℕ)) (A v) := by
    have h : A * T ^ (i : ℕ) = T ^ (i : ℕ) * A := (show Commute A T from hA).pow_right _
    have := congrArg (fun f : Module.End K V => f v) h
    simpa only [Module.End.mul_apply] using this
  have eB : B ((T ^ (i : ℕ)) v) = (T ^ (i : ℕ)) (B v) := by
    have h : B * T ^ (i : ℕ) = T ^ (i : ℕ) * B := (show Commute B T from hB).pow_right _
    have := congrArg (fun f : Module.End K V => f v) h
    simpa only [Module.End.mul_apply] using this
  rw [eA, eB, hAB]

-- ============================================================
-- SECTION II: the centralizer dimension upper bound
-- ============================================================

/-- **Frobenius upper bound in the cyclic case.**  For `T` with a cyclic vector,
    the centralizer has `K`-dimension at most `dim_K V`.  Evaluation at the
    cyclic vector, `A ↦ A·v`, is an injective `K`-linear map from the centralizer
    into `V` (`commuting_end_eq_of_apply_eq`), so its domain has dimension at most
    `dim_K V`. -/
theorem finrank_centralizer_le_of_cyclic [FiniteDimensional K V]
    (T : Module.End K V) (v : V) (hcyc : IsEndCyclicVector T v) :
    Module.finrank K (Subalgebra.centralizer K ({T} : Set (Module.End K V)))
      ≤ Module.finrank K V := by
  set S := Subalgebra.centralizer K ({T} : Set (Module.End K V)) with hS_def
  -- evaluation at `v`, as a `K`-linear map on the centralizer submodule
  let L : ↥(Subalgebra.toSubmodule S) →ₗ[K] V :=
    { toFun := fun A => (A : Module.End K V) v
      map_add' := fun A B => by
        simp only [Submodule.coe_add, LinearMap.add_apply]
      map_smul' := fun c A => by
        simp only [Submodule.coe_smul, LinearMap.smul_apply, RingHom.id_apply] }
  -- `A ↦ A·v` is injective on the centralizer
  have hinj : Function.Injective L := by
    intro A B hAB
    have hAmem : (A : Module.End K V) ∈ S := (Subalgebra.mem_toSubmodule S).mp A.2
    have hBmem : (B : Module.End K V) ∈ S := (Subalgebra.mem_toSubmodule S).mp B.2
    have hAcomm : (A : Module.End K V) * T = T * (A : Module.End K V) := by
      have := (Subalgebra.mem_centralizer_iff K).mp hAmem T (Set.mem_singleton _)
      exact this.symm
    have hBcomm : (B : Module.End K V) * T = T * (B : Module.End K V) := by
      have := (Subalgebra.mem_centralizer_iff K).mp hBmem T (Set.mem_singleton _)
      exact this.symm
    apply Subtype.ext
    exact commuting_end_eq_of_apply_eq T v hcyc _ _ hAcomm hBcomm hAB
  calc Module.finrank K S
      = Module.finrank K (↥(Subalgebra.toSubmodule S)) := rfl
    _ ≤ Module.finrank K V := LinearMap.finrank_le_finrank_of_injective hinj

-- ============================================================
-- SECTION III: the Frobenius equality
-- ============================================================

/-- **Frobenius equality for a cyclic endomorphism.**  If `T : Module.End K V`
    (over a finite-dimensional `V`) has a cyclic vector, then its centralizer has
    `K`-dimension **exactly** `dim_K V`:

        dim_K C(T) = dim_K V.

    The general Frobenius bound `endK_centralizer_bound` gives `≥`; the
    cyclic-specific `finrank_centralizer_le_of_cyclic` gives `≤`.  This is the
    minimal-centralizer characterisation of nonderogatory operators — the
    dimension-count edge of the triangle `nonderogatory ⟺ cyclic ⟺ C(T) = K[T]`,
    lifted to the coordinate-free `Module.End` setting. -/
theorem finrank_centralizer_eq_of_cyclic [FiniteDimensional K V]
    (T : Module.End K V) (v : V) (hcyc : IsEndCyclicVector T v) :
    Module.finrank K (Subalgebra.centralizer K ({T} : Set (Module.End K V)))
      = Module.finrank K V :=
  le_antisymm (finrank_centralizer_le_of_cyclic T v hcyc)
    (CyclicCommutantConverse.endK_centralizer_bound T)

-- ============================================================
-- SECTION IV: the evaluation isomorphism  C(T) ≃ₗ[K] V
-- ============================================================

/-- **Evaluation at `v`**, `A ↦ A·v`, as a `K`-linear map from the centralizer
    submodule of `T` into `V`.  (Named form of the map used implicitly in
    `finrank_centralizer_le_of_cyclic`; here we upgrade it to an isomorphism.) -/
def centralizerEval (T : Module.End K V) (v : V) :
    ↥(Subalgebra.toSubmodule (Subalgebra.centralizer K ({T} : Set (Module.End K V))))
      →ₗ[K] V where
  toFun A := (A : Module.End K V) v
  map_add' A B := by simp only [Submodule.coe_add, LinearMap.add_apply]
  map_smul' c A := by simp only [Submodule.coe_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- Evaluation at a cyclic vector is injective on the centralizer: two operators
    commuting with `T` that agree on `v` are equal (`commuting_end_eq_of_apply_eq`). -/
theorem centralizerEval_injective [FiniteDimensional K V]
    (T : Module.End K V) (v : V) (hcyc : IsEndCyclicVector T v) :
    Function.Injective (centralizerEval T v) := by
  set S := Subalgebra.centralizer K ({T} : Set (Module.End K V)) with hS_def
  intro A B hAB
  have hAB' : (A : Module.End K V) v = (B : Module.End K V) v := hAB
  have hAmem : (A : Module.End K V) ∈ S := (Subalgebra.mem_toSubmodule S).mp A.2
  have hBmem : (B : Module.End K V) ∈ S := (Subalgebra.mem_toSubmodule S).mp B.2
  have hAcomm : (A : Module.End K V) * T = T * (A : Module.End K V) :=
    ((Subalgebra.mem_centralizer_iff K).mp hAmem T (Set.mem_singleton _)).symm
  have hBcomm : (B : Module.End K V) * T = T * (B : Module.End K V) :=
    ((Subalgebra.mem_centralizer_iff K).mp hBmem T (Set.mem_singleton _)).symm
  exact Subtype.ext (commuting_end_eq_of_apply_eq T v hcyc _ _ hAcomm hBcomm hAB')

/-- **The evaluation isomorphism.**  For `T : Module.End K V` (over a
    finite-dimensional `V`) with a cyclic vector `v`, evaluation at `v`,
    `A ↦ A·v`, is a `K`-linear **isomorphism** from the centralizer `C(T)` onto
    the whole space `V`:

        C(T) ≃ₗ[K] V,   A ↦ A·v.

    This strengthens the Frobenius dimension *equality*
    (`finrank_centralizer_eq_of_cyclic`) to a canonical *equivalence*: the map is
    injective by `centralizerEval_injective` and the two spaces have equal
    dimension, so it is bijective.  It is the `K`-linear shadow of the statement
    "`V` is a free rank-`1` module over the commutative ring `K[T] = C(T)`" — the
    module-theoretic content of `v` being a cyclic vector. -/
noncomputable def centralizerEvalEquiv [FiniteDimensional K V]
    (T : Module.End K V) (v : V) (hcyc : IsEndCyclicVector T v) :
    ↥(Subalgebra.toSubmodule (Subalgebra.centralizer K ({T} : Set (Module.End K V))))
      ≃ₗ[K] V :=
  (centralizerEval T v).linearEquivOfInjective
    (centralizerEval_injective T v hcyc)
    (finrank_centralizer_eq_of_cyclic T v hcyc)

@[simp]
theorem centralizerEvalEquiv_apply [FiniteDimensional K V]
    (T : Module.End K V) (v : V) (hcyc : IsEndCyclicVector T v)
    (A : ↥(Subalgebra.toSubmodule (Subalgebra.centralizer K ({T} : Set (Module.End K V))))) :
    centralizerEvalEquiv T v hcyc A = (A : Module.End K V) v := rfl

-- ============================================================
-- SECTION V: nonderogatory degree — deg(minpoly) = dim V for a cyclic T
-- ============================================================

/-- **Nonderogatory degree (forward direction).**  If `T : Module.End K V` (over a
    finite-dimensional `V`) has a cyclic vector `v`, then the minimal polynomial of
    `T` has degree exactly `dim_K V`:

        (minpoly K T).natDegree = finrank K V.

    This is the *nonderogatory* edge of the triple equivalence
    `nonderogatory ⟺ cyclic ⟺ C(T) = K[T]`, expressed through the minimal
    polynomial rather than the centralizer dimension
    (`finrank_centralizer_eq_of_cyclic`).  Both inequalities are elementary:

    * `≥` : the minimal polynomial is a *nonzero* annihilator of `T`, hence
      `(minpoly K T) v = 0`; were its degree `< dim V`, cyclicity
      (`IsEndCyclicVector`) would force `minpoly K T = 0`, impossible for an
      integral element (`minpoly.ne_zero`, `LinearMap.isIntegral`).
    * `≤` : Cayley–Hamilton (`LinearMap.aeval_self_charpoly`) makes `minpoly K T`
      divide the characteristic polynomial, whose degree is `dim V`
      (`LinearMap.charpoly_natDegree`).

    Together with `minpoly` dividing `charpoly` this also gives `minpoly = charpoly`
    in the cyclic case, but only the degree equality is recorded here. -/
theorem minpoly_natDegree_eq_finrank_of_cyclic [FiniteDimensional K V]
    (T : Module.End K V) (v : V) (hcyc : IsEndCyclicVector T v) :
    (minpoly K T).natDegree = Module.finrank K V := by
  have hint : IsIntegral K T := LinearMap.isIntegral T
  have hne : minpoly K T ≠ 0 := minpoly.ne_zero hint
  have haeval : (aeval T) (minpoly K T) = 0 := minpoly.aeval K T
  -- lower bound: a nonzero annihilator of degree `< n` contradicts cyclicity
  have hge : Module.finrank K V ≤ (minpoly K T).natDegree := by
    by_contra h
    push_neg at h
    have hv0 : (aeval T (minpoly K T)) v = 0 := by rw [haeval]; simp
    exact hne (hcyc (minpoly K T) h hv0)
  -- upper bound: minpoly divides the characteristic polynomial (Cayley–Hamilton)
  have hle : (minpoly K T).natDegree ≤ Module.finrank K V := by
    have hdvd : minpoly K T ∣ T.charpoly := minpoly.dvd K T (LinearMap.aeval_self_charpoly T)
    have hcp_ne : T.charpoly ≠ 0 := T.charpoly_monic.ne_zero
    have hdeg : (minpoly K T).natDegree ≤ T.charpoly.natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd hcp_ne
    rwa [LinearMap.charpoly_natDegree] at hdeg
  omega

end EndCyclicCommutant

end
