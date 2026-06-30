import Mathlib

/-
# Similarity Invariants of Square Matrices

Two square matrices `A` and `B` over a commutative ring `R` are **similar** if `B = P A P⁻¹`
for some invertible `P`. Similarity is the matrix-level shadow of "same linear map in a
different basis", and the quantities preserved by a change of basis — the determinant, the
trace, and the characteristic polynomial — are exactly the similarity invariants.

Mathlib proves each invariance separately as `Matrix.det_units_conj`,
`Matrix.trace_units_conj`, and `Matrix.charpoly_units_conj`, but states neither a named
similarity relation nor a unified "these are all invariants" theorem. This file packages
the relation `Similar`, proves it is an equivalence relation, and collects the three
invariants together, with the corollary that similar matrices have the same eigenvalues
(the multiset of characteristic-polynomial roots).

Absent from Mathlib.
-/

namespace MatrixSimilarityInvariantsOQ01

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- Two square matrices are **similar** if one is a conjugate of the other by an invertible
matrix: `B = P * A * P⁻¹`. -/
def Similar (A B : Matrix n n R) : Prop :=
  ∃ P : (Matrix n n R)ˣ, B = P.val * A * P⁻¹.val

@[refl]
theorem Similar.refl (A : Matrix n n R) : Similar A A :=
  ⟨1, by simp⟩

theorem Similar.symm {A B : Matrix n n R} (h : Similar A B) : Similar B A := by
  obtain ⟨P, rfl⟩ := h
  refine ⟨P⁻¹, ?_⟩
  simp [mul_assoc]

theorem Similar.trans {A B C : Matrix n n R} (hab : Similar A B) (hbc : Similar B C) :
    Similar A C := by
  obtain ⟨P, rfl⟩ := hab
  obtain ⟨Q, rfl⟩ := hbc
  refine ⟨Q * P, ?_⟩
  simp [Units.val_mul, mul_assoc, _root_.mul_inv_rev]

/-- Similarity is an equivalence relation on square matrices. -/
theorem similar_equivalence : Equivalence (Similar (n := n) (R := R)) :=
  ⟨Similar.refl, Similar.symm, Similar.trans⟩

/-- The setoid of square matrices up to similarity. -/
def similarSetoid : Setoid (Matrix n n R) :=
  ⟨Similar, similar_equivalence⟩

/-- **Determinant is a similarity invariant.** -/
theorem Similar.det_eq {A B : Matrix n n R} (h : Similar A B) : B.det = A.det := by
  obtain ⟨P, rfl⟩ := h
  exact Matrix.det_units_conj P A

/-- **Trace is a similarity invariant.** -/
theorem Similar.trace_eq {A B : Matrix n n R} (h : Similar A B) : B.trace = A.trace := by
  obtain ⟨P, rfl⟩ := h
  exact Matrix.trace_units_conj P A

/-- **The characteristic polynomial is a similarity invariant.** -/
theorem Similar.charpoly_eq {A B : Matrix n n R} (h : Similar A B) :
    B.charpoly = A.charpoly := by
  obtain ⟨P, rfl⟩ := h
  exact Matrix.charpoly_units_conj P A

/-- **Similar matrices have the same eigenvalues**, i.e. the same multiset of
characteristic-polynomial roots (here over the base ring `R`). -/
theorem Similar.charpoly_roots_eq [IsDomain R] {A B : Matrix n n R} (h : Similar A B) :
    B.charpoly.roots = A.charpoly.roots :=
  congrArg Polynomial.roots h.charpoly_eq

/-- The three classical invariants, packaged together: similar matrices share their
determinant, trace, and characteristic polynomial. -/
theorem Similar.invariants {A B : Matrix n n R} (h : Similar A B) :
    B.det = A.det ∧ B.trace = A.trace ∧ B.charpoly = A.charpoly :=
  ⟨h.det_eq, h.trace_eq, h.charpoly_eq⟩

end MatrixSimilarityInvariantsOQ01
