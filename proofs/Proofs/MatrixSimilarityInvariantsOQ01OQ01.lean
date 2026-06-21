import Mathlib

/-
# Rank, Nullity, and Invertibility Are Similarity Invariants

Two square matrices `A` and `B` over a commutative ring `R` are **similar** when
`B = P A P⁻¹` for an invertible `P` — the matrix-level shadow of "the same linear map
written in a different basis".  The companion entry [oq-01]
(`MatrixSimilarityInvariantsOQ01`) collects the three *classical* similarity invariants:
the determinant, the trace, and the characteristic polynomial.

This entry adds the **rank / nullity / invertibility** layer, which is exactly the data a
change of basis cannot see about a linear map:

* `Similar.rank_eq` — **rank is a similarity invariant**, over *any* commutative ring.
  The proof is the conceptual one: conjugation is left- and right-multiplication by
  invertible matrices, and multiplying by an invertible matrix does not change the rank
  (`Matrix.rank_mul_eq_right_of_isUnit_det`, `Matrix.rank_mul_eq_left_of_isUnit_det`).
* `Similar.isUnit_iff` / `Similar.isUnit_det_iff` — **invertibility is a similarity
  invariant**: `B` is a unit iff `A` is, equivalently `det B` is a unit iff `det A` is.
  Again over any commutative ring (in fact any monoid for the matrix form), since
  multiplying by units preserves unit-ness.
* `rank_add_nullity` — the **rank–nullity theorem** in the matrix idiom over a field:
  `rank A + nullity A = n`, where `nullity A` is the dimension of the kernel of the
  associated linear map `A.mulVecLin`.
* `Similar.nullity_eq` — **nullity is a similarity invariant** over a field, an immediate
  consequence of `Similar.rank_eq` and `rank_add_nullity`.
* `nullity_eq_zero_iff_rank_eq_card` — the bridge tying the two pictures together:
  a square matrix over a field has trivial kernel iff it has full rank, the algebraic
  shadow of "injective = surjective = bijective" for endomorphisms of a finite-dimensional
  space.

Mathlib has the *ingredients* (`Matrix.rank_mul_eq_left_of_isUnit_det`,
`LinearMap.finrank_range_add_finrank_ker`, `Matrix.isUnit_iff_isUnit_det`) but states
neither a named `Similar` relation nor the packaged "rank, nullity and invertibility are
similarity invariants" theorems.  Absent from Mathlib.
-/

namespace MatrixSimilarityInvariantsOQ01OQ01

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- Two square matrices are **similar** if one is a conjugate of the other by an invertible
matrix: `B = P * A * P⁻¹`.  (Same definition as the companion entry [oq-01].) -/
def Similar (A B : Matrix n n R) : Prop :=
  ∃ P : (Matrix n n R)ˣ, B = P.val * A * P⁻¹.val

@[refl]
theorem Similar.refl (A : Matrix n n R) : Similar A A :=
  ⟨1, by simp⟩

theorem Similar.symm {A B : Matrix n n R} (h : Similar A B) : Similar B A := by
  obtain ⟨P, rfl⟩ := h
  exact ⟨P⁻¹, by simp [mul_assoc]⟩

/-! ## Invertibility is a similarity invariant -/

/-- **Invertibility is a similarity invariant.** `B` is a unit iff `A` is.  This holds for
any monoid, but we state it for matrices over a commutative ring. -/
theorem Similar.isUnit_iff {A B : Matrix n n R} (h : Similar A B) :
    IsUnit B ↔ IsUnit A := by
  obtain ⟨P, rfl⟩ := h
  rw [Units.isUnit_mul_units, Units.isUnit_units_mul]

/-- **Invertibility via the determinant.** `det B` is a unit iff `det A` is.  (Equivalent
to `Similar.isUnit_iff` through `Matrix.isUnit_iff_isUnit_det`, and the form one checks in
practice.) -/
theorem Similar.isUnit_det_iff {A B : Matrix n n R} (h : Similar A B) :
    IsUnit B.det ↔ IsUnit A.det := by
  rw [← isUnit_iff_isUnit_det, ← isUnit_iff_isUnit_det]
  exact h.isUnit_iff

/-! ## Rank is a similarity invariant -/

/-- **Rank is a similarity invariant**, over any commutative ring.  Conjugation is
left-multiplication by the unit `P` and right-multiplication by the unit `P⁻¹`, and neither
changes the rank. -/
theorem Similar.rank_eq {A B : Matrix n n R} (h : Similar A B) : B.rank = A.rank := by
  obtain ⟨P, rfl⟩ := h
  rw [rank_mul_eq_left_of_isUnit_det _ _
        ((isUnit_iff_isUnit_det _).mp (P⁻¹).isUnit),
      rank_mul_eq_right_of_isUnit_det _ _
        ((isUnit_iff_isUnit_det _).mp P.isUnit)]

/-! ## Nullity (over a field) -/

section Field

variable {K : Type*} [Field K]

/-- The **nullity** of a square matrix is the dimension of the kernel of its associated
linear map `A.mulVecLin : (n → K) →ₗ[K] (n → K)`. -/
noncomputable def nullity (A : Matrix n n K) : ℕ :=
  finrank K (LinearMap.ker A.mulVecLin)

omit [DecidableEq n] in
/-- **Rank–nullity theorem, matrix form.** For a square matrix over a field,
`rank A + nullity A = n`. -/
theorem rank_add_nullity (A : Matrix n n K) :
    A.rank + nullity A = Fintype.card n := by
  rw [Matrix.rank, nullity, LinearMap.finrank_range_add_finrank_ker, finrank_pi]

/-- **Nullity is a similarity invariant** over a field — immediate from `Similar.rank_eq`
and rank–nullity. -/
theorem Similar.nullity_eq {A B : Matrix n n K} (h : Similar A B) :
    nullity B = nullity A := by
  have hr := h.rank_eq
  have hA := rank_add_nullity A
  have hB := rank_add_nullity B
  omega

omit [DecidableEq n] in
/-- **Trivial kernel ⇔ full rank.** A square matrix over a field has nullity zero iff it has
full rank `n`; the algebraic form of "injective ⇔ surjective ⇔ bijective" for an
endomorphism of a finite-dimensional space. -/
theorem nullity_eq_zero_iff_rank_eq_card (A : Matrix n n K) :
    nullity A = 0 ↔ A.rank = Fintype.card n := by
  have := rank_add_nullity A
  omega

end Field

/-! ## Packaged statement -/

/-- The rank/invertibility invariants packaged together: similar matrices share their rank,
and one is invertible iff the other is. -/
theorem Similar.invariants {A B : Matrix n n R} (h : Similar A B) :
    B.rank = A.rank ∧ (IsUnit B ↔ IsUnit A) :=
  ⟨h.rank_eq, h.isUnit_iff⟩

end MatrixSimilarityInvariantsOQ01OQ01
