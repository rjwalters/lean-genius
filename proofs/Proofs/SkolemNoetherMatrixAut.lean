/-
  Skolem-Noether Theorem: K-Algebra Automorphisms of Mₙ(K) Are Inner
  (cayley-hamilton-minpoly-oq-02-oq-01-oq-01)

  Every K-algebra automorphism of the matrix algebra Mₙ(K) over a field K
  is an inner automorphism, i.e., conjugation by an invertible matrix.

  This file:
  1. Defines inner automorphisms of a K-algebra
  2. Proves inner automorphisms form a subgroup of the automorphism group
  3. States the Skolem-Noether theorem for Mₙ(K) (axiomatized)
  4. Derives consequences: the automorphism group modulo inner auts is trivial,
     and every automorphism preserves the minimal polynomial

  Background: The parent file CayleyHamiltonMinpolyOQ02OQ01.lean constructs
  conjAlgEquiv P (conjugation by P as an AlgEquiv) and notes that the
  Skolem-Noether theorem would show ALL automorphisms have this form.
  This file completes that picture.

  The Skolem-Noether theorem is a deep result in algebra. The standard proof
  uses the theory of simple modules over simple rings:
  - Mₙ(K) is a simple ring (no nontrivial two-sided ideals)
  - Kⁿ is the unique simple Mₙ(K)-module up to isomorphism
  - Any automorphism φ makes Kⁿ into a new module via the twisted action
  - By uniqueness, the original and twisted modules are isomorphic
  - The module isomorphism gives the conjugating matrix

  Since formalizing Artin-Wedderburn theory is beyond the scope of this
  session, the main theorem is axiomatized with full mathematical justification.
-/
import Mathlib

namespace SkolemNoether

variable {K : Type*} [Field K]
variable {n : Type*} [DecidableEq n] [Fintype n]

/-
  Part I: Conjugation Automorphism

  We re-derive the conjugation AlgEquiv here (originally from
  CayleyHamiltonMinpolyOQ02OQ01.lean) to keep this file self-contained.
-/

/-- Conjugation by an invertible matrix P defines a K-algebra automorphism
    on Mat(n,K). Maps A ↦ P⁻¹AP with inverse A ↦ PAP⁻¹. -/
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

/-
  Part II: Inner Automorphisms

  An automorphism φ of a K-algebra R is *inner* if φ = conjAlgEquiv P
  for some unit P. For matrix algebras, this means φ(A) = P⁻¹AP.
-/

/-- An automorphism of Mat(n,K) is inner if it equals conjugation by
    some invertible matrix. -/
def IsInnerAut (φ : Matrix n n K ≃ₐ[K] Matrix n n K) : Prop :=
  ∃ P : (Matrix n n K)ˣ, ∀ A : Matrix n n K, φ A = P⁻¹.val * A * P.val

/-- Conjugation by P is inner (tautological). -/
theorem conjAlgEquiv_isInner (P : (Matrix n n K)ˣ) :
    IsInnerAut (conjAlgEquiv P) :=
  ⟨P, fun _ => rfl⟩

/-- The identity automorphism is inner (conjugation by 1). -/
theorem isInnerAut_id : IsInnerAut (AlgEquiv.refl : Matrix n n K ≃ₐ[K] Matrix n n K) := by
  refine ⟨1, fun A => ?_⟩
  simp

/-- The inverse of an inner automorphism is inner.
    If φ = conj(P), then φ⁻¹ = conj(P⁻¹). -/
theorem isInnerAut_symm {φ : Matrix n n K ≃ₐ[K] Matrix n n K}
    (h : IsInnerAut φ) : IsInnerAut φ.symm := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P⁻¹, fun A => ?_⟩
  have key : φ.symm A = P.val * A * P⁻¹.val := by
    apply φ.injective
    rw [AlgEquiv.apply_symm_apply, hP]
    symm
    calc P⁻¹.val * (P.val * A * P⁻¹.val) * P.val
        = (P⁻¹.val * P.val) * A * (P⁻¹.val * P.val) := by simp only [mul_assoc]
      _ = 1 * A * 1 := by rw [Units.inv_mul]
      _ = A := by simp
  rw [key, show (P⁻¹ : (Matrix n n K)ˣ)⁻¹ = P from inv_inv P]

/-- The composition of two inner automorphisms is inner.
    If φ = conj(P) and ψ = conj(Q), then ψ ∘ φ = conj(PQ). -/
theorem isInnerAut_trans {φ ψ : Matrix n n K ≃ₐ[K] Matrix n n K}
    (hφ : IsInnerAut φ) (hψ : IsInnerAut ψ) : IsInnerAut (φ.trans ψ) := by
  obtain ⟨P, hP⟩ := hφ
  obtain ⟨Q, hQ⟩ := hψ
  refine ⟨P * Q, fun A => ?_⟩
  simp only [AlgEquiv.trans_apply]
  rw [hP, hQ]
  symm
  rw [show (P * Q)⁻¹.val = Q⁻¹.val * P⁻¹.val from by simp [mul_inv_rev, Units.val_mul]]
  rw [show (P * Q).val = P.val * Q.val from Units.val_mul P Q]
  simp only [mul_assoc]

/-
  Part III: Skolem-Noether Theorem for Mₙ(K)

  The Skolem-Noether theorem states that every K-algebra automorphism of
  the matrix algebra Mₙ(K) is inner. This is a deep theorem whose standard
  proof uses the uniqueness of simple modules over simple Artinian rings.

  Proof sketch (not formalized here):
  1. Mₙ(K) is a simple ring — its only two-sided ideals are {0} and Mₙ(K)
  2. Kⁿ is the unique simple left Mₙ(K)-module (up to isomorphism)
  3. Given automorphism φ, define a "twisted" module V_φ where M acts as φ(M)
  4. V_φ is also a simple Mₙ(K)-module of dimension n
  5. By uniqueness, V ≅ V_φ as Mₙ(K)-modules
  6. The module isomorphism f : Kⁿ → Kⁿ is K-linear, hence f ∈ GL_n(K)
  7. The intertwining condition f(Mv) = φ(M)f(v) gives φ(M) = fMf⁻¹

  Formalizing this proof requires Artin-Wedderburn theory, which is substantial
  foundational work beyond the scope of this formalization. The theorem is
  axiomatized below with its precise mathematical statement.
-/

/-- **Skolem-Noether Theorem for Mₙ(K)**: Every K-algebra automorphism of the
    matrix algebra Mₙ(K) over a field K is an inner automorphism.

    That is, for any φ : Mₙ(K) ≃ₐ[K] Mₙ(K), there exists an invertible
    matrix P such that φ(A) = P⁻¹AP for all matrices A.

    This is a classical result in abstract algebra. The proof uses the fact
    that Mₙ(K) is a central simple K-algebra and all simple modules over
    it are isomorphic. See Artin, "Algebra", Chapter 12 or
    Lang, "Algebra", Chapter XVII, §5. -/
axiom skolemNoether [Nonempty n] (φ : Matrix n n K ≃ₐ[K] Matrix n n K) :
    IsInnerAut φ

/-
  Part IV: Consequences

  The Skolem-Noether theorem has several important consequences for matrix
  algebras. Combined with the results from CayleyHamiltonMinpolyOQ02OQ01.lean,
  it gives a complete picture of K-algebra automorphisms of Mₙ(K).
-/

section Consequences

variable [Nonempty n]

/-- Every K-algebra automorphism of Mₙ(K) is conjugation by some specific
    invertible matrix. This is the "extraction" form of Skolem-Noether. -/
theorem exists_conjugating_matrix (φ : Matrix n n K ≃ₐ[K] Matrix n n K) :
    ∃ P : (Matrix n n K)ˣ, ∀ A, φ A = P⁻¹.val * A * P.val :=
  skolemNoether φ

/-- The Skolem-Noether theorem shows that Aut_K(Mₙ(K)) ≅ PGLₙ(K).
    Every automorphism is inner (given by some P), and two units P, Q
    give the same automorphism iff P = cQ for some scalar c.
    This is the surjection part: every automorphism comes from a unit. -/
theorem surjection_units_to_aut (φ : Matrix n n K ≃ₐ[K] Matrix n n K) :
    ∃ P : (Matrix n n K)ˣ, φ = conjAlgEquiv P := by
  obtain ⟨P, hP⟩ := skolemNoether φ
  exact ⟨P, AlgEquiv.ext (fun A => hP A)⟩

end Consequences

/-- Any K-algebra automorphism of Mₙ(K) preserves the minimal polynomial.
    This follows directly from minpoly.algEquiv_eq (independent of Skolem-Noether),
    but gains conceptual clarity: the automorphism is just conjugation. -/
theorem automorphism_preserves_minpoly (φ : Matrix n n K ≃ₐ[K] Matrix n n K)
    (A : Matrix n n K) : minpoly K (φ A) = minpoly K A :=
  minpoly.algEquiv_eq φ A

/-- Two K-algebra automorphisms of Mₙ(K) that agree on all matrices are equal.
    Combined with Skolem-Noether, this means automorphisms are determined by
    their conjugating matrices (up to scalars). -/
theorem aut_ext {φ ψ : Matrix n n K ≃ₐ[K] Matrix n n K}
    (h : ∀ A : Matrix n n K, φ A = ψ A) : φ = ψ :=
  AlgEquiv.ext h

/-
  Part V: The Trivial Case n = 1

  When n = 1, Mₙ(K) ≅ K, and the only K-algebra automorphism of K is
  the identity. This is directly provable without the Skolem-Noether axiom.
-/

/-- For 1×1 matrices over K, every K-algebra automorphism is the identity.
    This is the trivial case of Skolem-Noether: M₁(K) ≅ K, and K has no
    nontrivial K-algebra automorphisms. -/
theorem skolemNoether_one
    (φ : Matrix (Fin 1) (Fin 1) K ≃ₐ[K] Matrix (Fin 1) (Fin 1) K)
    (A : Matrix (Fin 1) (Fin 1) K) : φ A = A := by
  have hA : A = (A 0 0) • (1 : Matrix (Fin 1) (Fin 1) K) := by
    ext i j; fin_cases i; fin_cases j; simp
  have hsmul : (A 0 0) • (1 : Matrix (Fin 1) (Fin 1) K) =
      algebraMap K (Matrix (Fin 1) (Fin 1) K) (A 0 0) := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [hA, hsmul, φ.commutes]

/-- For 1×1 matrices, every automorphism is inner (proved, no axiom needed). -/
theorem skolemNoether_one_inner
    (φ : Matrix (Fin 1) (Fin 1) K ≃ₐ[K] Matrix (Fin 1) (Fin 1) K) :
    IsInnerAut φ := by
  refine ⟨1, fun A => ?_⟩
  simp [skolemNoether_one φ A]

/-
  Summary:

  This file establishes the formal framework for the Skolem-Noether theorem
  in the context of matrix algebras Mₙ(K) over a field K:

  PROVED:
  - conjAlgEquiv: conjugation by invertible P as a K-algebra automorphism
  - IsInnerAut: formal definition of inner automorphisms
  - Inner automorphisms form a group (id, symm, trans closure)
  - The n=1 case: every automorphism of M₁(K) is the identity (hence inner)
  - Every automorphism preserves minpoly (from minpoly.algEquiv_eq)

  AXIOMATIZED:
  - skolemNoether: every K-algebra automorphism of Mₙ(K) is inner
    (requires Artin-Wedderburn theory / simple module uniqueness)

  DERIVED (from the axiom):
  - exists_conjugating_matrix: extraction form of Skolem-Noether
  - surjection_units_to_aut: Aut_K(Mₙ(K)) = Inn(Mₙ(K))
  - automorphism_preserves_minpoly: minpoly invariance (also provable
    directly from minpoly.algEquiv_eq)
-/

end SkolemNoether
