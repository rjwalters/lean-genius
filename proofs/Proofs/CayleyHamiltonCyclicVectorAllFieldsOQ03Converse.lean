/-
  Converse direction for OQ-03 (operator cyclic vector): cyclic ⟹ nonderogatory.

  The headline file `CayleyHamiltonCyclicVectorAllFieldsOQ03.lean` proves the
  FORWARD operator statement: a nonderogatory operator on a finite-dimensional
  space has a cyclic vector
  (`operator_nonderogatory_has_cyclic_vector` and its span-form recast
  `operator_nonderogatory_has_span_cyclic_vector`).

  This companion supplies the missing CONVERSE in the span vocabulary of the
  registered `NonderogatoryModule` development: if some vector's Krylov orbit
  `{v, T v, T² v, …}` spans the whole space, then `T` is nonderogatory, i.e.
  `(minpoly K T).natDegree = finrank K V`. Together with the forward span-form
  capstone this closes the biconditional

      T is nonderogatory  ⟺  T has a span-cyclic vector

  recovering OQ-03's headline "minpoly = charpoly ⟺ cyclic vector" as a genuine
  `↔` at the operator level.

  Proof of the converse:
    * Let `d = (minpoly K T).natDegree` and `W = span_K {v, T v, …, Tᵈ⁻¹ v}`.
    * The registered lemma `cyclicSubspace_le_minpoly_degree` shows every Krylov
      power `Tᵏ v` (for `k ≥ d`) already lies in `W`; the small powers lie in
      `W` by definition. Hence the cyclic subspace `span_K {Tᵏ v : k}` is `≤ W`.
    * If the cyclic subspace is `⊤`, then `W = ⊤`, so
      `finrank K V = finrank K W ≤ d` (a span of `d` vectors).
    * Always `d ≤ finrank K V` because `minpoly K T ∣ T.charpoly` and
      `T.charpoly.natDegree = finrank K V`.  Antisymmetry gives `d = finrank K V`.

  0 sorry / 0 axiom.  Uses only Mathlib + the registered OQ-03 infrastructure.
-/
import Mathlib
import Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ03

open Polynomial

namespace CyclicVectorOperator

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- **Converse (span form).** If the Krylov orbit of `v` under `T` spans the
    whole finite-dimensional space, then `T` is nonderogatory:
    `(minpoly K T).natDegree = finrank K V`.

    This is the missing direction of the OQ-03 biconditional; the forward
    direction is `operator_nonderogatory_has_span_cyclic_vector`. -/
theorem span_cyclic_implies_nonderogatoryOp [FiniteDimensional K V]
    (T : Module.End K V) (v : V)
    (hv : NonderogatoryModule.cyclicSubspace T v = ⊤) :
    IsNonderogatoryOp T := by
  set d := (minpoly K T).natDegree with hd_def
  have hint : IsIntegral K T := IsIntegral.of_finite K T
  -- `W` is the span of the first `d` Krylov powers of `v`.
  set W : Submodule K V :=
    Submodule.span K (Set.range fun i : Fin d => (T ^ (i : ℕ)) v) with hW_def
  -- Every Krylov power lies in `W`: small powers by definition, large powers via
  -- the minimal-polynomial relation (registered lemma).
  have horbit : ∀ k : ℕ, (T ^ k) v ∈ W := by
    intro k
    by_cases hk : k < d
    · exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
    · exact NonderogatoryModule.cyclicSubspace_le_minpoly_degree T hint v k (by omega)
  -- Hence the cyclic subspace is contained in `W`.
  have hsub : NonderogatoryModule.cyclicSubspace T v ≤ W := by
    have heq : NonderogatoryModule.cyclicSubspace T v
        = Submodule.span K (Set.range fun k : ℕ => (T ^ k) v) := rfl
    rw [heq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact horbit k
  -- Since the cyclic subspace is `⊤`, so is `W`.
  have hWtop : W = ⊤ := top_le_iff.mp (hv ▸ hsub)
  -- `finrank K V ≤ d`, because `W = ⊤` is spanned by `d` vectors.
  have hle : Module.finrank K V ≤ d := by
    have hcard := finrank_range_le_card (R := K) (fun i : Fin d => (T ^ (i : ℕ)) v)
    rw [Fintype.card_fin] at hcard
    calc Module.finrank K V
        = Module.finrank K
            (Submodule.span K (Set.range fun i : Fin d => (T ^ (i : ℕ)) v)) := by
          rw [hWtop, finrank_top]
      _ = (Set.range fun i : Fin d => (T ^ (i : ℕ)) v).finrank K := rfl
      _ ≤ d := hcard
  -- `d ≤ finrank K V`, because `minpoly K T ∣ T.charpoly` and the characteristic
  -- polynomial has degree `finrank K V`.
  have hge : d ≤ Module.finrank K V := by
    have hdvd : minpoly K T ∣ T.charpoly := LinearMap.minpoly_dvd_charpoly T
    have hne : T.charpoly ≠ 0 := T.charpoly_monic.ne_zero
    have hbound := Polynomial.natDegree_le_of_dvd hdvd hne
    rwa [LinearMap.charpoly_natDegree] at hbound
  show (minpoly K T).natDegree = Module.finrank K V
  exact le_antisymm hge hle

/-- **Headline biconditional (operator span form).** A finite-dimensional
    operator is nonderogatory (`minpoly = charpoly`, i.e.
    `(minpoly K T).natDegree = finrank K V`) **iff** it admits a span-cyclic
    vector — a vector whose Krylov orbit spans the whole space.

    Forward: `operator_nonderogatory_has_span_cyclic_vector`.
    Converse: `span_cyclic_implies_nonderogatoryOp`. -/
theorem nonderogatoryOp_iff_exists_span_cyclic [FiniteDimensional K V]
    (T : Module.End K V) :
    IsNonderogatoryOp T ↔ ∃ v, NonderogatoryModule.cyclicSubspace T v = ⊤ := by
  constructor
  · intro h
    exact operator_nonderogatory_has_span_cyclic_vector T h
  · rintro ⟨v, hv⟩
    exact span_cyclic_implies_nonderogatoryOp T v hv

end CyclicVectorOperator
