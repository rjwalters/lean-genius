/-
  Minimal Polynomial Generalization to K-Algebras
  (cayley-hamilton-minpoly-oq-02-oq-01)

  Open Question: Can the minimal polynomial theory be generalized from
  matrices to abstract K-algebras? If two elements of an algebra are
  related by an isomorphism, they should have the same minimal polynomial.

  Answer: YES. Mathlib provides minpoly.algEquiv_eq and minpoly.algHom_eq
  establishing that minimal polynomials are invariant under K-algebra
  isomorphisms (and more generally, injective K-algebra homomorphisms).

  This file:
  1. States the abstract invariance results from Mathlib
  2. Constructs conjugation by an invertible matrix as an AlgEquiv
  3. Derives the matrix similarity result as a direct corollary
  4. Proves additional corollaries connecting abstract and concrete theory

  The key insight is that matrix similarity A ~ P⁻¹AP is precisely an
  AlgEquiv on Mat(n,K), so the abstract theory immediately yields the
  matrix-level result without any manual proof.
-/
import Mathlib

namespace MinpolyKAlgebra

variable {K : Type*} [Field K]

/-
  Part I: Abstract Theory (from Mathlib)

  Mathlib provides two key results:

  minpoly.algEquiv_eq : For any AlgEquiv f : B ≃ₐ[A] B',
    minpoly A (f x) = minpoly A x

  minpoly.algHom_eq : For any injective AlgHom f : B →ₐ[A] B',
    minpoly A (f x) = minpoly A x

  These establish that the minimal polynomial is an invariant of any
  K-algebra element under isomorphisms (and injective homomorphisms).
  We re-export these for reference.
-/

section Abstract

variable {S : Type*} [Ring S] [Algebra K S]
variable {T : Type*} [Ring T] [Algebra K T]

/-- The minimal polynomial is invariant under algebra equivalences.
    This is Mathlib's minpoly.algEquiv_eq. -/
theorem minpoly_invariant_algEquiv (φ : S ≃ₐ[K] T) (x : S) :
    minpoly K (φ x) = minpoly K x :=
  minpoly.algEquiv_eq φ x

/-- The minimal polynomial is invariant under injective algebra homomorphisms.
    This is Mathlib's minpoly.algHom_eq. -/
theorem minpoly_invariant_algHom (φ : S →ₐ[K] T) (hφ : Function.Injective φ) (x : S) :
    minpoly K (φ x) = minpoly K x :=
  minpoly.algHom_eq φ hφ x

end Abstract

/-
  Part II: Conjugation as an AlgEquiv

  In CayleyHamiltonMinpolyOQ02.lean, conjugation was defined as an
  AlgHom (algebra endomorphism). Here we upgrade it to an AlgEquiv
  (algebra automorphism), which is the correct abstraction since
  conjugation by an invertible matrix is invertible.
-/

section MatrixConjugation

variable {n : Type*} [DecidableEq n] [Fintype n]

/-- Conjugation by an invertible matrix P defines a K-algebra automorphism
    on Mat(n,K).

    The map: A ↦ P⁻¹AP
    Inverse:  A ↦ PAP⁻¹ -/
noncomputable def conjAlgEquiv (P : (Matrix n n K)ˣ) :
    Matrix n n K ≃ₐ[K] Matrix n n K where
  toFun := fun A => P⁻¹.val * A * P.val
  invFun := fun A => P.val * A * P⁻¹.val
  left_inv := fun A => by
    show P.val * (P⁻¹.val * A * P.val) * P⁻¹.val = A
    calc P.val * (P⁻¹.val * A * P.val) * P⁻¹.val
        = (P.val * P⁻¹.val) * A * (P.val * P⁻¹.val) := by simp only [mul_assoc]
      _ = 1 * A * 1 := by rw [Units.mul_inv]
      _ = A := by simp
  right_inv := fun A => by
    show P⁻¹.val * (P.val * A * P⁻¹.val) * P.val = A
    calc P⁻¹.val * (P.val * A * P⁻¹.val) * P.val
        = (P⁻¹.val * P.val) * A * (P⁻¹.val * P.val) := by simp only [mul_assoc]
      _ = 1 * A * 1 := by rw [Units.inv_mul]
      _ = A := by simp
  map_mul' := fun A B => by
    show P⁻¹.val * (A * B) * P.val
        = (P⁻¹.val * A * P.val) * (P⁻¹.val * B * P.val)
    have h : P.val * P⁻¹.val = 1 := Units.mul_inv P
    symm
    calc (P⁻¹.val * A * P.val) * (P⁻¹.val * B * P.val)
        = P⁻¹.val * A * (P.val * P⁻¹.val) * B * P.val := by simp only [mul_assoc]
      _ = P⁻¹.val * A * 1 * B * P.val := by rw [h]
      _ = P⁻¹.val * (A * B) * P.val := by simp only [mul_one, mul_assoc]
  map_add' := fun A B => by
    show P⁻¹.val * (A + B) * P.val
        = P⁻¹.val * A * P.val + P⁻¹.val * B * P.val
    simp [mul_add, add_mul]
  commutes' := fun c => by
    show P⁻¹.val * (algebraMap K (Matrix n n K) c) * P.val
        = algebraMap K (Matrix n n K) c
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm]
    rw [mul_one, Units.inv_mul]

/-- Matrix similarity preserves minpoly, derived from abstract theory.

    Unlike CayleyHamiltonMinpolyOQ02.lean which proves this from scratch
    using minpoly.unique, here we derive it as a corollary of
    the abstract minpoly.algEquiv_eq applied to the conjugation AlgEquiv. -/
theorem minpoly_similar_via_abstract (A : Matrix n n K) (P : (Matrix n n K)ˣ) :
    minpoly K A = minpoly K (P⁻¹.val * A * P.val) :=
  (minpoly.algEquiv_eq (conjAlgEquiv P) A).symm

/-- Conjugation by the inverse: minpoly(PAP⁻¹) = minpoly(A). -/
theorem minpoly_conj_inv_via_abstract (A : Matrix n n K) (P : (Matrix n n K)ˣ) :
    minpoly K (P.val * A * P⁻¹.val) = minpoly K A := by
  have key : P.val * A * P⁻¹.val = conjAlgEquiv P⁻¹ A := by
    show P.val * A * P⁻¹.val = (P⁻¹)⁻¹.val * A * (P⁻¹).val
    rw [show (P⁻¹ : (Matrix n n K)ˣ)⁻¹ = P from inv_inv P]
  rw [key]
  exact minpoly.algEquiv_eq (conjAlgEquiv P⁻¹) A

end MatrixConjugation

/-
  Part III: Applications and Corollaries
-/

section Applications

variable {n : Type*} [DecidableEq n] [Fintype n]

/-- If two matrices are related by any K-algebra automorphism φ of Mat(n,K),
    they have the same minimal polynomial. This is strictly more general than
    similarity: every inner automorphism (conjugation) is an AlgEquiv, but
    for simple algebras the Skolem-Noether theorem says all automorphisms
    are inner. -/
theorem minpoly_algAut_invariant
    (φ : Matrix n n K ≃ₐ[K] Matrix n n K) (A : Matrix n n K) :
    minpoly K (φ A) = minpoly K A :=
  minpoly.algEquiv_eq φ A

/-- For any subalgebra S of Mat(n,K), the inclusion map preserves
    minimal polynomials. This means the minimal polynomial computed
    within a subalgebra agrees with the one computed in the full
    matrix algebra. -/
theorem minpoly_subalgebra_eq (S : Subalgebra K (Matrix n n K))
    (x : S) : minpoly K x = minpoly K (x : Matrix n n K) :=
  (minpoly.algHom_eq S.val Subtype.val_injective x).symm

/-- If A and B are similar (B = P⁻¹AP), then for ANY K-algebra R and
    ANY K-algebra homomorphism φ : Mat(n,K) →ₐ[K] R, we have
    minpoly K (φ A) = minpoly K (φ B).

    This shows that similarity is truly an algebra-theoretic notion:
    similar matrices are indistinguishable to any algebra homomorphism. -/
theorem minpoly_similar_under_algHom
    {R : Type*} [Ring R] [Algebra K R]
    (φ : Matrix n n K →ₐ[K] R) (hφ : Function.Injective φ)
    (A : Matrix n n K) (P : (Matrix n n K)ˣ) :
    minpoly K (φ A) = minpoly K (φ (P⁻¹.val * A * P.val)) := by
  rw [minpoly.algHom_eq φ hφ A, minpoly.algHom_eq φ hφ]
  exact minpoly_similar_via_abstract A P

/-- The conjugation AlgEquiv is symmetric: the symm of conjugation by P
    is conjugation by P⁻¹. -/
theorem conjAlgEquiv_symm (P : (Matrix n n K)ˣ) (A : Matrix n n K) :
    (conjAlgEquiv P).symm A = P.val * A * P⁻¹.val := by
  rfl

/-- Composing conjugation by Q after conjugation by P gives
    conjugation by PQ. -/
theorem conjAlgEquiv_trans (P Q : (Matrix n n K)ˣ) (A : Matrix n n K) :
    (conjAlgEquiv P).trans (conjAlgEquiv Q) A = conjAlgEquiv (P * Q) A := by
  simp only [AlgEquiv.trans_apply, conjAlgEquiv]
  show Q⁻¹.val * (P⁻¹.val * A * P.val) * Q.val
      = (P * Q)⁻¹.val * A * (P * Q).val
  rw [show (P * Q)⁻¹.val = Q⁻¹.val * P⁻¹.val from by
    simp [mul_inv_rev, Units.val_mul]]
  rw [show (P * Q).val = P.val * Q.val from Units.val_mul P Q]
  simp only [mul_assoc]

end Applications

/-
  Part IV: Summary

  The answer to the open question is definitively YES:

  1. Mathlib's minpoly.algEquiv_eq proves that minpoly K (φ x) = minpoly K x
     for any K-algebra isomorphism φ : R ≃ₐ[K] S.

  2. Matrix similarity (A ~ P⁻¹AP) is a special case: conjugation defines
     an AlgEquiv on Mat(n,K), so the abstract result applies directly.

  3. Even stronger: minpoly.algHom_eq shows invariance under any INJECTIVE
     K-algebra homomorphism, not just isomorphisms. This means:
     - Subalgebra inclusions preserve minpoly
     - Any embedding of one algebra into another preserves minpoly

  The proof architecture demonstrates that minpoly is a fundamental
  K-algebra invariant, not merely a matrix invariant.
-/

end MinpolyKAlgebra
