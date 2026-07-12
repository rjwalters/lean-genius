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

end BezoutPrimitive
