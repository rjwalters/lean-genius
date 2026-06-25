import Mathlib

/-
# The Minimal Polynomial Is a Similarity Invariant

Two square matrices `A` and `B` over a commutative ring `R` are **similar** when
`B = P A P⁻¹` for an invertible `P` — the matrix-level shadow of "the same linear map
written in a different basis".  The parent entry [oq-01]
(`MatrixSimilarityInvariantsOQ01`) collects the three *classical* similarity invariants —
the **determinant**, the **trace**, and the **characteristic polynomial** — and the sibling
[oq-01-oq-01] adds rank / nullity / invertibility.

This entry adds the **minimal polynomial**, a strictly *finer* invariant than the
characteristic polynomial:

* `Similar.minpoly_eq` — **the minimal polynomial is a similarity invariant**, over *any*
  commutative ring `R`.  The proof is the conceptual one: conjugation by an invertible `P`
  is an *algebra automorphism* of the matrix ring, and any algebra equivalence preserves the
  minimal polynomial (`minpoly.algEquiv_eq`).  We realise the conjugation automorphism as
  `MulSemiringAction.toAlgEquiv` for the `ConjAct (Matrix n n R)ˣ` action.
* `Similar.minpoly_eq'`, `minpolyOfSimilarityClass` — the corollary that `minpoly` is
  well-defined on the similarity setoid (it descends to the quotient by `Similar`).
* `notSimilar_zero_stdNilpotent`, `charpoly_zero_eq_stdNilpotent` — a worked **separating
  example** over a field: the `2 × 2` zero matrix and the single nilpotent Jordan block
  `!![0,1;0,0]` share the characteristic polynomial `X ^ 2` yet have *different* minimal
  polynomials (`X` versus a non-`X` polynomial), so they are **not similar**.  This both
  certifies that `minpoly` is strictly finer than `charpoly` and shows the new invariant
  doing real work as a non-similarity certificate via the contrapositive of
  `Similar.minpoly_eq`.

Mathlib has `minpoly.algEquiv_eq` (invariance of `minpoly` under any algebra equivalence)
and the conjugation `AlgEquiv` (`MulSemiringAction.toAlgEquiv` for `ConjAct`) separately, but
states **no** theorem that similar matrices share a minimal polynomial.  This leaf supplies
exactly that bridge in the parent's `Similar` vocabulary.  Absent from Mathlib.
-/

namespace MatrixSimilarityInvariantsOQ01OQ02

open Matrix Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- Two square matrices are **similar** if one is a conjugate of the other by an invertible
matrix: `B = P * A * P⁻¹`.  (Same relation as the parent entry.) -/
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

/-!
## The minimal polynomial is a similarity invariant

The engine is `minpoly.algEquiv_eq`: the minimal polynomial is invariant under any algebra
equivalence.  Conjugation by an invertible matrix `P` is such an equivalence — the image of
`A` under the `ConjAct (Matrix n n R)ˣ` algebra action — so `minpoly R (P A P⁻¹) = minpoly R A`.
-/

/-- Conjugation by an invertible matrix `P`, packaged as the algebra automorphism
`MulSemiringAction.toAlgEquiv` of the `ConjAct (Matrix n n R)ˣ` action, sends `A` to
`P * A * P⁻¹`. -/
theorem conj_algEquiv_apply (P : (Matrix n n R)ˣ) (A : Matrix n n R) :
    (MulSemiringAction.toAlgEquiv R (Matrix n n R) (ConjAct.toConjAct P)) A
      = P.val * A * P⁻¹.val := by
  rw [MulSemiringAction.toAlgEquiv_apply, ConjAct.units_smul_def]
  simp

/-- **The minimal polynomial is a similarity invariant.**  If `B = P A P⁻¹` then
`minpoly R B = minpoly R A`, over any commutative ring `R`. -/
theorem Similar.minpoly_eq {A B : Matrix n n R} (h : Similar A B) :
    minpoly R B = minpoly R A := by
  obtain ⟨P, rfl⟩ := h
  rw [← conj_algEquiv_apply P A, minpoly.algEquiv_eq]

/-- Symmetric restatement: the minimal polynomial of the two matrices in a similarity
agrees, oriented as a well-definedness statement. -/
theorem Similar.minpoly_eq' {A B : Matrix n n R} (h : Similar A B) :
    minpoly R A = minpoly R B :=
  (h.minpoly_eq).symm

/-- The minimal polynomial **descends to the similarity setoid**: it is a well-defined
function on similarity classes of square matrices. -/
noncomputable def minpolyOfSimilarityClass :
    Quotient (similarSetoid (n := n) (R := R)) → R[X] :=
  Quotient.lift (fun A => minpoly R A) fun _ _ h => (Similar.minpoly_eq h).symm

@[simp]
theorem minpolyOfSimilarityClass_mk (A : Matrix n n R) :
    minpolyOfSimilarityClass (Quotient.mk (similarSetoid) A) = minpoly R A :=
  rfl

/-!
## A separating example: `minpoly` is strictly finer than `charpoly`

Over any field `F`, the `2 × 2` zero matrix and the single nilpotent Jordan block
`!![0,1;0,0]` have the **same** characteristic polynomial `X ^ 2` but **different** minimal
polynomials — so the minimal polynomial detects a non-similarity that the characteristic
polynomial cannot.  This exhibits `minpoly` as a strictly finer invariant and uses
`Similar.minpoly_eq` contrapositively as a non-similarity certificate.
-/

section Separating

variable {F : Type*} [Field F]

/-- The single nilpotent `2 × 2` Jordan block `!![0,1;0,0]`. -/
def stdNilpotent : Matrix (Fin 2) (Fin 2) F := !![0, 1; 0, 0]

theorem stdNilpotent_ne_zero : (stdNilpotent : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
  intro h
  have h01 : (stdNilpotent : Matrix (Fin 2) (Fin 2) F) 0 1 = 1 := by simp [stdNilpotent]
  rw [h] at h01
  simp at h01

/-- The zero matrix and the nilpotent block share the characteristic polynomial `X ^ 2`. -/
theorem charpoly_zero_eq_stdNilpotent :
    (0 : Matrix (Fin 2) (Fin 2) F).charpoly
      = (stdNilpotent : Matrix (Fin 2) (Fin 2) F).charpoly := by
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two]
  simp [stdNilpotent, Matrix.trace_fin_two, Matrix.det_fin_two]

/-- The minimal polynomial of the zero matrix is `X`. -/
theorem minpoly_zero_matrix :
    minpoly F (0 : Matrix (Fin 2) (Fin 2) F) = X :=
  minpoly.zero F (Matrix (Fin 2) (Fin 2) F)

/-- The minimal polynomial of the nilpotent block is **not** `X` (it is annihilated only by
a higher-degree polynomial, since the block itself is nonzero). -/
theorem minpoly_stdNilpotent_ne_X :
    minpoly F (stdNilpotent : Matrix (Fin 2) (Fin 2) F) ≠ X := by
  intro hX
  have hae := minpoly.aeval F (stdNilpotent : Matrix (Fin 2) (Fin 2) F)
  rw [hX] at hae
  rw [aeval_X] at hae
  exact stdNilpotent_ne_zero hae

/-- The two matrices have **different** minimal polynomials. -/
theorem minpoly_zero_ne_stdNilpotent :
    minpoly F (0 : Matrix (Fin 2) (Fin 2) F)
      ≠ minpoly F (stdNilpotent : Matrix (Fin 2) (Fin 2) F) := by
  rw [minpoly_zero_matrix]
  exact fun h => minpoly_stdNilpotent_ne_X h.symm

/-- **Non-similarity certificate.**  The zero matrix and the nilpotent block `!![0,1;0,0]`
are *not similar*, even though they share the characteristic polynomial `X ^ 2`: their
minimal polynomials differ, so `Similar.minpoly_eq` rules out a similarity.  This is the
classical witness that the minimal polynomial is a strictly finer similarity invariant than
the characteristic polynomial. -/
theorem notSimilar_zero_stdNilpotent :
    ¬ Similar (0 : Matrix (Fin 2) (Fin 2) F) stdNilpotent := by
  intro h
  exact minpoly_zero_ne_stdNilpotent (h.minpoly_eq).symm

end Separating

end MatrixSimilarityInvariantsOQ01OQ02
