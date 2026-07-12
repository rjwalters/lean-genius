/-
# Unimodular completion: a primitive vector extends to a `ℤ`-basis

Research: bezout-identity-oq-01-oq-02-oq-02

The parent file `BezoutIdentityOQ01OQ02OQ02.lean` establishes that `SLₙ(ℤ)` acts
transitively on primitive integer vectors (`exists_sl_mulVec_basis_of_isPrimitive`,
`isPrimitive_iff_exists_sl_column`) and repeatedly asserts, in prose, the classical
consequence that

> a primitive integer vector **extends to a `ℤ`-basis** of `ℤⁿ` (unimodular
> completion): the columns of `SLₙ(ℤ)` are exactly the primitive vectors.

That statement is only ever phrased there through the *matrix* datum `↑ₘA *ᵥ eₖ = v`.
This file turns it into the honest object it is describing: an actual
`Basis (Fin n) ℤ (Fin n → ℤ)` one of whose members is the prescribed vector.  Nothing
here is axiomatized — everything reduces to the parent transitivity theorem and the
standard `Matrix`/`Basis` bridge, so the whole file is `propext`/`Classical.choice`/
`Quot.sound`-only.

* `slColumnBasis A` — the `ℤ`-basis of `ℤⁿ` given by the **columns** of `A ∈ SLₙ(ℤ)`,
  built as the image of the standard basis under the linear equivalence
  `SpecialLinearGroup.toLin' A`.  `slColumnBasis_apply` identifies its `k`-th member
  with the column `↑ₘA *ᵥ eₖ`.
* `slColumnBasis_isPrimitive` — every member of such a basis is primitive (the parent
  `orbit_e_isPrimitive` restated for the basis object).
* `isPrimitive_of_mem_basis` — the **converse in every dimension**: *any* member of
  *any* `ℤ`-basis of `ℤⁿ` is primitive.  Uses the dual functional `b.coord i`, which
  provides an integer dual vector `w` with `w · (b i) = 1`.  No dimension hypothesis.
* `exists_basis_apply_eq_of_isPrimitive` — the **capstone (`n ≥ 2`)**: for any
  prescribed slot `i`, a primitive vector `v` is the `i`-th member of some `ℤ`-basis of
  `ℤⁿ`.  This is unimodular completion with the completing basis produced explicitly.
* `isPrimitive_iff_mem_basis` — the resulting **characterization (`n ≥ 2`)**: a vector
  is primitive iff it is a member of some `ℤ`-basis of `ℤⁿ`.
-/
import Mathlib
import Proofs.BezoutIdentityOQ01OQ02OQ02

namespace BezoutPrimitive

open Matrix Module

variable {n : ℕ}

local notation:1024 "↑ₘ" A:1024 =>
  ((A : Matrix.SpecialLinearGroup (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ)

/-! ### The column basis of a unimodular matrix -/

/-- The `ℤ`-basis of `ℤⁿ` whose `k`-th member is the `k`-th **column** of a unimodular
matrix `A ∈ SLₙ(ℤ)`.  It is the image of the standard basis `Pi.basisFun` under the
linear equivalence `SpecialLinearGroup.toLin' A`; being an isomorphism carries a basis to
a basis, and its action on `eₖ` extracts the `k`-th column of `A`. -/
noncomputable def slColumnBasis (A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    Basis (Fin n) ℤ (Fin n → ℤ) :=
  (Pi.basisFun ℤ (Fin n)).map (Matrix.SpecialLinearGroup.toLin' A)

/-- The `k`-th member of `slColumnBasis A` is the `k`-th column `↑ₘA *ᵥ eₖ` of `A`. -/
@[simp]
theorem slColumnBasis_apply (A : Matrix.SpecialLinearGroup (Fin n) ℤ) (k : Fin n) :
    slColumnBasis A k = ↑ₘA *ᵥ Pi.single k (1 : ℤ) := by
  rw [slColumnBasis, Basis.map_apply, Pi.basisFun_apply,
    Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]

/-- Every member of a column basis of a unimodular matrix is primitive.  This is the
parent `orbit_e_isPrimitive` (any column of an `SLₙ(ℤ)` matrix is primitive), transported
onto the `Basis` object. -/
theorem slColumnBasis_isPrimitive (A : Matrix.SpecialLinearGroup (Fin n) ℤ) (k : Fin n) :
    IsPrimitive (slColumnBasis A k) := by
  rw [slColumnBasis_apply]
  exact orbit_e_isPrimitive A k

/-! ### The converse: members of any `ℤ`-basis are primitive -/

/-- **Members of a `ℤ`-basis are primitive (all `n`).**  If `b` is any `ℤ`-basis of `ℤⁿ`
then each `b i` is a primitive vector.  The dual coordinate functional `b.coord i` is a
`ℤ`-linear map `ℤⁿ → ℤ` sending `b i` to `1`; representing it by its values on the
standard basis gives an explicit integer dual vector `w` with `w · (b i) = 1`, which is
exactly primitivity.  No dimension hypothesis is needed — this even resolves the `n = 1`
case, where `(−1)` is a one-element basis of `ℤ¹` and is indeed primitive. -/
theorem isPrimitive_of_mem_basis (b : Basis (Fin n) ℤ (Fin n → ℤ)) (i : Fin n) :
    IsPrimitive (b i) := by
  classical
  -- The functional `b.coord i` equals dotting with `w j = b.coord i (eⱼ)`.
  have key : ∀ x : Fin n → ℤ,
      (b.coord i) x = ∑ j, x j * (b.coord i) (Pi.single j (1 : ℤ)) := by
    intro x
    conv_lhs => rw [← (Pi.basisFun ℤ (Fin n)).sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.basisFun_repr, Pi.basisFun_apply, map_smul, smul_eq_mul]
  refine ⟨fun j => (b.coord i) (Pi.single j (1 : ℤ)), ?_⟩
  have hcoord : (b.coord i) (b i) = 1 := by
    rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]
  calc (fun j => (b.coord i) (Pi.single j (1 : ℤ))) ⬝ᵥ b i
      = ∑ j, (b i) j * (b.coord i) (Pi.single j (1 : ℤ)) := by
        simp only [dotProduct]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = (b.coord i) (b i) := (key (b i)).symm
    _ = 1 := hcoord

/-! ### Unimodular completion for `n ≥ 2` -/

/-- **Unimodular completion (`n ≥ 2`), prescribed slot.**  Given a primitive vector `v`
and any index `i`, there is a `ℤ`-basis of `ℤⁿ` whose `i`-th member is exactly `v`.  The
completing basis is produced explicitly: transitivity (`exists_sl_mulVec_basis_of_isPrimitive`)
gives `U ∈ SLₙ(ℤ)` with `↑ₘU *ᵥ v = eᵢ`, and then `v` is the `i`-th column of `U⁻¹`, i.e.
the `i`-th member of `slColumnBasis U⁻¹`.

Taking `i` to be the first coordinate places `v` as the leading basis vector, matching the
parent `bezoutSL` construction which carries a coprime pair onto `e₁`. -/
theorem exists_basis_apply_eq_of_isPrimitive (hn : 1 < n) {v : Fin n → ℤ}
    (hv : IsPrimitive v) (i : Fin n) :
    ∃ b : Basis (Fin n) ℤ (Fin n → ℤ), b i = v := by
  obtain ⟨U, hU⟩ := exists_sl_mulVec_basis_of_isPrimitive hn hv i
  refine ⟨slColumnBasis U⁻¹, ?_⟩
  rw [slColumnBasis_apply, ← hU, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

/-- **A primitive vector extends to a `ℤ`-basis (`n ≥ 2`).**  Existence form of unimodular
completion: every primitive vector is a member of some `ℤ`-basis of `ℤⁿ`. -/
theorem exists_basis_mem_of_isPrimitive (hn : 1 < n) {v : Fin n → ℤ}
    (hv : IsPrimitive v) :
    ∃ (b : Basis (Fin n) ℤ (Fin n → ℤ)) (i : Fin n), b i = v := by
  obtain ⟨b, hb⟩ := exists_basis_apply_eq_of_isPrimitive hn hv ⟨0, by omega⟩
  exact ⟨b, ⟨0, by omega⟩, hb⟩

/-- **Primitive ⇔ member of a `ℤ`-basis (`n ≥ 2`).**  Combining unimodular completion
(forward) with `isPrimitive_of_mem_basis` (backward) pins down primitivity as *exactly*
the property of extending to a `ℤ`-basis of `ℤⁿ`: for `n ≥ 2` the primitive vectors are
precisely the vectors that occur as a member of some basis. -/
theorem isPrimitive_iff_mem_basis (hn : 1 < n) (v : Fin n → ℤ) :
    IsPrimitive v ↔ ∃ (b : Basis (Fin n) ℤ (Fin n → ℤ)) (i : Fin n), b i = v := by
  refine ⟨exists_basis_mem_of_isPrimitive hn, ?_⟩
  rintro ⟨b, i, rfl⟩
  exact isPrimitive_of_mem_basis b i

/-! ### Removing the dimension hypothesis: the characterization holds for **all** `n`

The `1 < n` hypothesis on the *forward* direction above comes only from the transitivity
theorem `exists_sl_mulVec_basis_of_isPrimitive`, which is genuinely false at `n = 1`
(the group `SL₁(ℤ)` is trivial, so `(1)` and `(−1)` lie in distinct orbits — see the
parent file's `not_forall_isPrimitive_sl_equiv_fin_one`).  But the *basis* characterization
is about **unimodular** completion (transition determinant `±1`, i.e. `GLₙ(ℤ)`), not the
`SL` orbit: at `n = 1` a primitive vector is `(±1)`, and `{(−1)}` is perfectly well a
`ℤ`-basis of `ℤ¹` even though `(−1)` is not an `SL₁` image of `(1)`.  Supplying that single
missing case (`Basis.unitsSMul` scales the standard basis by the unit `v 0 = ±1`) upgrades
the characterization to an **all-`n`** statement. -/

/-- **Unimodular completion at `n = 1`.**  A primitive vector `v : Fin 1 → ℤ` (so `v 0`
is a unit `±1`) is the sole member of a `ℤ`-basis of `ℤ¹`, namely the standard basis scaled
by the unit `v 0`.  This is the case the `SL`-based `exists_basis_apply_eq_of_isPrimitive`
cannot reach, because it needs a determinant-`+1` completion. -/
theorem exists_basis_apply_eq_of_isPrimitive_fin_one {v : Fin 1 → ℤ}
    (hv : IsPrimitive v) (i : Fin 1) :
    ∃ b : Basis (Fin 1) ℤ (Fin 1 → ℤ), b i = v := by
  obtain ⟨w, hw⟩ := hv
  have hdot : w ⬝ᵥ v = w 0 * v 0 := by simp [dotProduct]
  have hwv : w 0 * v 0 = 1 := by rw [← hdot]; exact hw
  have hvw : v 0 * w 0 = 1 := by rw [mul_comm]; exact hwv
  -- `v 0` is a unit `±1`; build it explicitly with inverse `w 0`.
  let u : ℤˣ := ⟨v 0, w 0, hvw, hwv⟩
  refine ⟨(Pi.basisFun ℤ (Fin 1)).unitsSMul (fun _ => u), ?_⟩
  have h0 : i = 0 := Subsingleton.elim _ _
  subst h0
  rw [Basis.unitsSMul_apply]
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  simp only [Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_same, Units.smul_def,
    smul_eq_mul, mul_one]
  rfl

/-- **Unimodular completion, all `n`, prescribed slot.**  For every `n`, a primitive vector
`v` is the `i`-th member of some `ℤ`-basis of `ℤⁿ`.  For `n ≥ 2` this is the `SL`-based
`exists_basis_apply_eq_of_isPrimitive`; for `n = 1` it is the unit-scaling above; `n = 0`
has no index `i`. -/
theorem exists_basis_apply_eq_of_isPrimitive_all {v : Fin n → ℤ}
    (hv : IsPrimitive v) (i : Fin n) :
    ∃ b : Basis (Fin n) ℤ (Fin n → ℤ), b i = v := by
  match n, v, hv, i with
  | 0, _, _, i => exact i.elim0
  | 1, v, hv, i => exact exists_basis_apply_eq_of_isPrimitive_fin_one hv i
  | (_ + 2), v, hv, i => exact exists_basis_apply_eq_of_isPrimitive (by omega) hv i

/-- **A primitive vector extends to a `ℤ`-basis, all `n`.**  Existence form of unimodular
completion valid in every dimension.  (At `n = 0` there are no primitive vectors — the empty
dot product cannot equal `1` — so the statement is vacuously true.) -/
theorem exists_basis_mem_of_isPrimitive_all {v : Fin n → ℤ} (hv : IsPrimitive v) :
    ∃ (b : Basis (Fin n) ℤ (Fin n → ℤ)) (i : Fin n), b i = v := by
  match n, v, hv with
  | 0, v, hv =>
      obtain ⟨w, hw⟩ := hv
      simp only [dotProduct, Finset.univ_eq_empty, Finset.sum_empty] at hw
      exact absurd hw zero_ne_one
  | (k + 1), v, hv =>
      obtain ⟨b, hb⟩ := exists_basis_apply_eq_of_isPrimitive_all hv (0 : Fin (k + 1))
      exact ⟨b, 0, hb⟩

/-- **Primitive ⇔ member of a `ℤ`-basis, in every dimension.**  The all-`n` upgrade of
`isPrimitive_iff_mem_basis`: with the `n = 1` case supplied, primitivity is *exactly* the
property of occurring as a member of some `ℤ`-basis of `ℤⁿ`, with no dimension hypothesis. -/
theorem isPrimitive_iff_mem_basis_all (v : Fin n → ℤ) :
    IsPrimitive v ↔ ∃ (b : Basis (Fin n) ℤ (Fin n → ℤ)) (i : Fin n), b i = v := by
  refine ⟨exists_basis_mem_of_isPrimitive_all, ?_⟩
  rintro ⟨b, i, rfl⟩
  exact isPrimitive_of_mem_basis b i


/-! ### Orientation-preserving (determinant `+1`) completion, and the sharp `n = 1` obstruction

The `n ≥ 2` completions built above are not merely `GLₙ(ℤ)` (transition determinant `±1`)
but genuinely `SLₙ(ℤ)` (determinant `+1`): the column basis of a unimodular matrix inherits
its determinant `+1`, so the completing basis is **orientation-preserving**.  This turns the
prose `SL`-versus-`GL` distinction of the parent file into a machine-checked statement.  The
distinction is sharp exactly at `n = 1`: there the primitive vector `(−1)` provably admits *no*
determinant-`+1` completion — its unique completion `{(−1)}` has determinant `−1`.  So the
orientation obstruction that keeps the `SL`-action from being transitive at `n = 1`
(`not_forall_isPrimitive_sl_equiv_fin_one`) is *precisely* the failure of orientation-preserving
completion, and it evaporates for every `n ≥ 2`. -/

/-- The determinant of the column basis of `A ∈ SLₙ(ℤ)`, read against the standard basis, is
`+1`.  Indeed `Basis.toMatrix` of `slColumnBasis A` is literally `↑ₘA` (its `(i,j)` entry is the
`i`-th coordinate of the `j`-th column of `A`), whose determinant is `1` by definition of
`SLₙ(ℤ)`. -/
@[simp]
theorem slColumnBasis_det (A : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    (Pi.basisFun ℤ (Fin n)).det ⇑(slColumnBasis A) = 1 := by
  rw [Basis.det_apply]
  have hmat : (Pi.basisFun ℤ (Fin n)).toMatrix ⇑(slColumnBasis A) = ↑ₘA := by
    ext i j
    rw [Basis.toMatrix_apply, Pi.basisFun_repr, slColumnBasis_apply]
    show ((↑ₘA) i) ⬝ᵥ (Pi.single j (1 : ℤ)) = ↑ₘA i j
    rw [dotProduct_single _ (1 : ℤ), mul_one]
  rw [hmat]
  exact Matrix.SpecialLinearGroup.det_coe A

/-- **Orientation-preserving unimodular completion (`n ≥ 2`, prescribed slot).**  A primitive
vector `v` is the `i`-th member of some `ℤ`-basis of `ℤⁿ` **whose determinant against the
standard basis is `+1`** — i.e. the completion can always be taken in `SLₙ(ℤ)`, not just
`GLₙ(ℤ)`.  Same construction as `exists_basis_apply_eq_of_isPrimitive`, now recording that the
completing basis `slColumnBasis U⁻¹` is orientation-preserving via `slColumnBasis_det`. -/
theorem exists_basis_apply_eq_of_isPrimitive_det_one (hn : 1 < n) {v : Fin n → ℤ}
    (hv : IsPrimitive v) (i : Fin n) :
    ∃ b : Basis (Fin n) ℤ (Fin n → ℤ),
      b i = v ∧ (Pi.basisFun ℤ (Fin n)).det ⇑b = 1 := by
  obtain ⟨U, hU⟩ := exists_sl_mulVec_basis_of_isPrimitive hn hv i
  refine ⟨slColumnBasis U⁻¹, ?_, slColumnBasis_det _⟩
  rw [slColumnBasis_apply, ← hU, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

/-- **Primitive ⇔ orientation-preserving completion (`n ≥ 2`).**  For `n ≥ 2` a vector is
primitive iff it occurs as a member of some `ℤ`-basis of determinant `+1`.  The extra
determinant datum costs nothing on the forward direction (the `SL`-completion already has it)
and is discarded on the backward direction (`isPrimitive_of_mem_basis` needs only membership).
So at `n ≥ 2` primitivity is *exactly* orientation-preserving completability, the same strength
as plain completability (`isPrimitive_iff_mem_basis`). -/
theorem isPrimitive_iff_orientation_completion (hn : 1 < n) (v : Fin n → ℤ) (i : Fin n) :
    IsPrimitive v ↔
      ∃ b : Basis (Fin n) ℤ (Fin n → ℤ),
        b i = v ∧ (Pi.basisFun ℤ (Fin n)).det ⇑b = 1 := by
  refine ⟨fun hv => exists_basis_apply_eq_of_isPrimitive_det_one hn hv i, ?_⟩
  rintro ⟨b, rfl, -⟩
  exact isPrimitive_of_mem_basis b i

/-- The determinant of any `ℤ`-basis of `ℤ¹`, against the standard basis, is just its single
entry `b 0 0` (the `1 × 1` determinant).  This is the computational heart of the `n = 1`
orientation obstruction. -/
theorem basis_det_fin_one (b : Basis (Fin 1) ℤ (Fin 1 → ℤ)) :
    (Pi.basisFun ℤ (Fin 1)).det ⇑b = b 0 0 := by
  rw [Basis.det_apply, Matrix.det_fin_one, Basis.toMatrix_apply, Pi.basisFun_repr]

/-- **Sharp `n = 1` orientation dichotomy.**  A vector `v : Fin 1 → ℤ` admits a
determinant-`+1` completion iff `v 0 = 1`.  Forward: any completion `b` with `b 0 = v` has
determinant `b 0 0 = v 0`, forced to `1`.  Backward: when `v 0 = 1` the standard basis itself
is the (orientation-preserving) completion.  So at `n = 1` orientation-preserving completion is
*strictly* stronger than plain completion — every primitive `v` (i.e. `v 0 = ±1`) completes to
a basis, but only `v 0 = 1` completes with determinant `+1`. -/
theorem exists_det_one_completion_fin_one_iff (v : Fin 1 → ℤ) :
    (∃ b : Basis (Fin 1) ℤ (Fin 1 → ℤ),
        b 0 = v ∧ (Pi.basisFun ℤ (Fin 1)).det ⇑b = 1) ↔ v 0 = 1 := by
  constructor
  · rintro ⟨b, hb, hdet⟩
    rw [basis_det_fin_one, hb] at hdet
    exact hdet
  · intro hv0
    refine ⟨Pi.basisFun ℤ (Fin 1), ?_, Basis.det_self _⟩
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rw [Pi.basisFun_apply, Pi.single_eq_same]
    exact hv0.symm

/-- **The concrete orientation obstruction at `n = 1`.**  The primitive vector `(−1) : Fin 1 → ℤ`
extends to a `ℤ`-basis (namely `{(−1)}`, via `exists_basis_apply_eq_of_isPrimitive_fin_one`) but
to **no** basis of determinant `+1`.  This is the exact `n = 1` witness separating
orientation-preserving completion from plain completion, dual to the parent's
`not_forall_isPrimitive_sl_equiv_fin_one`. -/
theorem no_det_one_completion_neg_fin_one :
    ¬ ∃ b : Basis (Fin 1) ℤ (Fin 1 → ℤ),
        b 0 = (fun _ => -1) ∧ (Pi.basisFun ℤ (Fin 1)).det ⇑b = 1 := by
  rw [exists_det_one_completion_fin_one_iff]
  norm_num

/-! ### Module-theoretic form: a primitive vector spans a direct summand

The basis-membership characterization `isPrimitive_iff_mem_basis_all` is the
*coordinate* form of unimodular completion.  Its coordinate-free shadow is the
statement that the cyclic submodule `ℤ · v` is a **direct summand** of `ℤⁿ`: there
is a complementary submodule `K` with `ℤⁿ = ℤ·v ⊕ K`.  This is the classical
"primitive = saturated/pure = direct summand" theorem.  Unlike basis membership it
hands back a *canonical* complement: the kernel of the dual functional `x ↦ w · x`
supplied by primitivity (`w · v = 1`), giving the explicit internal direct sum
`ℤⁿ = ℤ·v ⊕ ker(w · –)`.  Everything stays `propext`/`Classical.choice`/`Quot.sound`-only. -/

/-- **Primitivity as a linear retraction.**  `v` is primitive iff it admits a
`ℤ`-linear functional `f : ℤⁿ → ℤ` with `f v = 1` — i.e. the inclusion
`ℤ → ℤⁿ, c ↦ c • v` has a `ℤ`-linear left inverse.  This is the coordinate-free
reading of the dot-product dual `w · v = 1`: the Bézout covector `w` becomes the
functional `x ↦ w · x`, and conversely a functional is recovered from its values on
the standard basis (`f x = ∑ⱼ xⱼ · f eⱼ`, the same evaluation used in
`isPrimitive_of_mem_basis`). -/
theorem isPrimitive_iff_exists_dual_functional (v : Fin n → ℤ) :
    IsPrimitive v ↔ ∃ f : (Fin n → ℤ) →ₗ[ℤ] ℤ, f v = 1 := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨{ toFun := fun x => w ⬝ᵥ x
              map_add' := fun x y => by
                simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]
              map_smul' := fun c x => by
                simp only [RingHom.id_apply, smul_eq_mul, dotProduct, Pi.smul_apply,
                  Finset.mul_sum]
                exact Finset.sum_congr rfl fun i _ => by ring }, hw⟩
  · rintro ⟨f, hf⟩
    refine ⟨fun j => f (Pi.single j (1 : ℤ)), ?_⟩
    have key : ∀ x : Fin n → ℤ, f x = ∑ j, x j * f (Pi.single j (1 : ℤ)) := by
      intro x
      conv_lhs => rw [← (Pi.basisFun ℤ (Fin n)).sum_repr x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.basisFun_repr, Pi.basisFun_apply, map_smul, smul_eq_mul]
    calc (fun j => f (Pi.single j (1 : ℤ))) ⬝ᵥ v
        = ∑ j, v j * f (Pi.single j (1 : ℤ)) := by
          simp only [dotProduct]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = f v := (key v).symm
      _ = 1 := hf

/-- **Canonical splitting from a dual functional.**  If a `ℤ`-linear functional `f`
sends `v` to `1`, then `ℤⁿ` is the internal direct sum of the line `ℤ · v` and the
hyperplane `ker f`: `IsCompl (ℤ · v) (ker f)`.  Disjointness: an element `c • v` of
the kernel has `0 = f (c • v) = c`, so it vanishes.  Codisjointness: `x` splits as
`(f x) • v + (x − (f x) • v)`, the first term on the line and the second in the
kernel (`f` of it is `f x − f x = 0`).  The idempotent `x ↦ (f x) • v` is the
projection onto the line along the kernel. -/
theorem isCompl_span_singleton_ker_of_apply_eq_one {v : Fin n → ℤ}
    {f : (Fin n → ℤ) →ₗ[ℤ] ℤ} (hf : f v = 1) :
    IsCompl (Submodule.span ℤ ({v} : Set (Fin n → ℤ))) (LinearMap.ker f) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hxk
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [LinearMap.mem_ker, map_smul, hf, smul_eq_mul, mul_one] at hxk
    rw [hxk, zero_smul]
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    rw [Submodule.mem_sup]
    refine ⟨f x • v, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v),
      x - f x • v, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub, map_smul, hf, smul_eq_mul, mul_one, sub_self]

/-- **A primitive vector generates a direct summand (canonical complement).**  For
primitive `v` there is a dual functional `f` with `f v = 1` for which
`ℤⁿ = ℤ·v ⊕ ker f`.  This records the completing decomposition *together with* the
functional that produces it — the canonical, basis-free unimodular completion. -/
theorem IsPrimitive.isCompl_span_singleton_ker {v : Fin n → ℤ} (hv : IsPrimitive v) :
    ∃ f : (Fin n → ℤ) →ₗ[ℤ] ℤ,
      f v = 1 ∧ IsCompl (Submodule.span ℤ ({v} : Set (Fin n → ℤ))) (LinearMap.ker f) := by
  obtain ⟨f, hf⟩ := (isPrimitive_iff_exists_dual_functional v).mp hv
  exact ⟨f, hf, isCompl_span_singleton_ker_of_apply_eq_one hf⟩

/-- **A primitive vector spans a direct summand (existence form).**  `ℤ·v` is a
direct summand of `ℤⁿ`: some complementary submodule `K` satisfies
`IsCompl (ℤ·v) K`.  This is the module-theoretic essence of unimodular completion,
complementary to the basis-membership form `isPrimitive_iff_mem_basis_all`. -/
theorem IsPrimitive.isCompl_span_singleton {v : Fin n → ℤ} (hv : IsPrimitive v) :
    ∃ K : Submodule ℤ (Fin n → ℤ),
      IsCompl (Submodule.span ℤ ({v} : Set (Fin n → ℤ))) K := by
  obtain ⟨f, _, hcompl⟩ := hv.isCompl_span_singleton_ker
  exact ⟨LinearMap.ker f, hcompl⟩

/-- **Converse: a complemented line has a primitive generator (`v ≠ 0`).**  If the
line `ℤ · v` is a direct summand of `ℤⁿ` and `v ≠ 0`, then `v` is primitive.  The
complementary projection `ℤⁿ ↠ ℤ·v` composed with the coordinate isomorphism
`ℤ·v ≃ ℤ` — available because `ℤⁿ` is torsion-free and `v ≠ 0` — is a functional
sending `v` to `1`, so `isPrimitive_iff_exists_dual_functional` closes it.  The
hypothesis `v ≠ 0` is essential: at `v = 0` the line is `⊥`, trivially complemented
by `⊤`, yet `0` is not primitive. -/
theorem isPrimitive_of_isCompl_span_singleton {v : Fin n → ℤ} (hv0 : v ≠ 0)
    {K : Submodule ℤ (Fin n → ℤ)}
    (h : IsCompl (Submodule.span ℤ ({v} : Set (Fin n → ℤ))) K) :
    IsPrimitive v := by
  rw [isPrimitive_iff_exists_dual_functional]
  have hv : v ∈ Submodule.span ℤ ({v} : Set (Fin n → ℤ)) :=
    Submodule.mem_span_singleton_self v
  refine ⟨(LinearEquiv.toSpanNonzeroSingleton ℤ (Fin n → ℤ) v hv0).symm.toLinearMap.comp
      ((Submodule.span ℤ ({v} : Set (Fin n → ℤ))).linearProjOfIsCompl K h), ?_⟩
  have hproj :
      (Submodule.span ℤ ({v} : Set (Fin n → ℤ))).linearProjOfIsCompl K h v = ⟨v, hv⟩ :=
    Submodule.linearProjOfIsCompl_apply_left h ⟨v, hv⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hproj, LinearEquiv.symm_apply_eq,
    LinearEquiv.toSpanNonzeroSingleton_one]

/-- **Primitive ⇔ its line is a direct summand (`v ≠ 0`).**  For a nonzero integer
vector `v`, primitivity is *exactly* the property that the cyclic submodule `ℤ · v`
splits off as a direct summand of `ℤⁿ`.  This is the coordinate-free counterpart of
the basis-membership characterization `isPrimitive_iff_mem_basis_all`, packaged as a
clean equivalence once the degenerate `v = 0` case (never primitive, always
`⊥`-complemented) is excluded by hypothesis. -/
theorem isPrimitive_iff_isCompl_span_singleton {v : Fin n → ℤ} (hv0 : v ≠ 0) :
    IsPrimitive v ↔
      ∃ K : Submodule ℤ (Fin n → ℤ),
        IsCompl (Submodule.span ℤ ({v} : Set (Fin n → ℤ))) K := by
  refine ⟨fun hv => hv.isCompl_span_singleton, ?_⟩
  rintro ⟨K, hK⟩
  exact isPrimitive_of_isCompl_span_singleton hv0 hK

end BezoutPrimitive
