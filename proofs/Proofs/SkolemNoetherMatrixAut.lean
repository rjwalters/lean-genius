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

set_option linter.deprecated false

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

  PROVED (no axioms):
  - center_iff_scalar: Center(Mₙ(K)) = K·I
  - scalar_commutes: scalar matrices commute with everything
  - off_diagonal_vanish_of_center: central matrices have zero off-diagonal
  - diagonal_constant_of_center: central matrices have equal diagonal entries
  - conjAlgEquiv_eq_iff_center: two units give same conjugation iff their
    ratio is central
  - conjAlgEquiv_injective_mod_center: conjugation separates units modulo center
-/

/-
  Part VI: Matrix Unit Product Lemmas

  Helper lemmas for computing products with standard basis matrices
  (matrix units E_ij). These support the center characterization.
-/

section MatrixUnitProducts

/-- Right-multiplying by the matrix unit E_ij extracts column i of A and
    places it in column j. Uses Finset.sum_eq_single for clean computation. -/
theorem mul_eij_entry (A : Matrix n n K) (i j : n) (k l : n) :
    (A * Matrix.stdBasisMatrix i j (1 : K)) k l = if l = j then A k i else 0 := by
  simp only [Matrix.mul_apply]
  by_cases hlj : l = j
  · subst hlj; rw [if_pos rfl]
    rw [Finset.sum_eq_single i]
    · simp [Matrix.stdBasisMatrix, Matrix.of_apply]
    · intro m _ hm; simp [Matrix.stdBasisMatrix, Matrix.of_apply, Ne.symm hm]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_neg hlj]
    apply Finset.sum_eq_zero
    intro m _; simp [Matrix.stdBasisMatrix, Matrix.of_apply, Ne.symm hlj]

/-- Left-multiplying by the matrix unit E_ij extracts row j of A and
    places it in row i. -/
theorem eij_mul_entry (A : Matrix n n K) (i j : n) (k l : n) :
    (Matrix.stdBasisMatrix i j (1 : K) * A) k l = if k = i then A j l else 0 := by
  simp only [Matrix.mul_apply]
  by_cases hki : k = i
  · subst hki; rw [if_pos rfl]
    rw [Finset.sum_eq_single j]
    · simp [Matrix.stdBasisMatrix, Matrix.of_apply]
    · intro m _ hm; simp [Matrix.stdBasisMatrix, Matrix.of_apply, Ne.symm hm]
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [if_neg hki]
    apply Finset.sum_eq_zero
    intro m _; simp [Matrix.stdBasisMatrix, Matrix.of_apply, Ne.symm hki]

end MatrixUnitProducts

/-
  Part VII: Center of Mₙ(K) = Scalar Matrices

  A matrix in the center of Mₙ(K) (commuting with all matrices) must be a
  scalar multiple of the identity. This is proved by testing commutativity
  against standard basis matrices E_ij:
  - E_ij for i ≠ j forces off-diagonal entries to vanish
  - E_ij for i ≠ j also forces all diagonal entries to be equal
-/

section Center

/-- A scalar matrix commutes with every matrix. -/
theorem scalar_commutes (c : K) (B : Matrix n n K) :
    c • (1 : Matrix n n K) * B = B * (c • (1 : Matrix n n K)) := by
  simp [smul_mul_assoc, mul_smul_comm]

/-- Off-diagonal entries of a central matrix are zero.
    Proof: test A against E_ji and examine the (i,i) entry.
    LHS: (A * E_ji)(i,i) = A(i,j) since column j of A goes to column i.
    RHS: (E_ji * A)(i,i) = 0 since i ≠ j means no contribution. -/
theorem off_diagonal_vanish_of_center (A : Matrix n n K)
    (hcomm : ∀ B : Matrix n n K, A * B = B * A)
    (i j : n) (hij : i ≠ j) : A i j = 0 := by
  have h := congr_fun (congr_fun (hcomm (Matrix.stdBasisMatrix j i (1 : K))) i) i
  rw [mul_eij_entry, eij_mul_entry] at h
  simp only [if_pos rfl] at h
  rwa [if_neg hij] at h

/-- Diagonal entries of a central matrix are all equal.
    Proof: test A against E_ij and examine the (i,j) entry.
    LHS: (A * E_ij)(i,j) = A(i,i) since column i of A goes to column j.
    RHS: (E_ij * A)(i,j) = A(j,j) since row j of A goes to row i. -/
theorem diagonal_constant_of_center [Nonempty n] (A : Matrix n n K)
    (hcomm : ∀ B : Matrix n n K, A * B = B * A)
    (i j : n) : A i i = A j j := by
  by_cases hij : i = j
  · rw [hij]
  · have h := congr_fun (congr_fun (hcomm (Matrix.stdBasisMatrix i j (1 : K))) i) j
    rw [mul_eij_entry, eij_mul_entry] at h
    simp only [if_pos rfl] at h
    exact h

/-- **Center of Mₙ(K) = K·I**: A matrix in Mₙ(K) commutes with all matrices
    if and only if it is a scalar multiple of the identity.
    This is a fundamental structural result about matrix algebras. -/
theorem center_iff_scalar [Nonempty n] (A : Matrix n n K) :
    (∀ B : Matrix n n K, A * B = B * A) ↔ ∃ c : K, A = c • (1 : Matrix n n K) := by
  constructor
  · intro hcomm
    obtain ⟨i₀⟩ := ‹Nonempty n›
    refine ⟨A i₀ i₀, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, eq_self_iff_true, if_true,
        mul_one]
      exact (diagonal_constant_of_center A hcomm i₀ i).symm
    · simp only [Matrix.smul_apply, Matrix.one_apply, if_neg hij, smul_zero]
      exact off_diagonal_vanish_of_center A hcomm i j hij
  · rintro ⟨c, rfl⟩
    exact scalar_commutes c

end Center

/-
  Part VIII: Conjugation Kernel and PGL Structure

  Two invertible matrices P, Q give the same conjugation automorphism
  conjAlgEquiv P = conjAlgEquiv Q if and only if QP⁻¹ is a scalar matrix.
  This determines the kernel of the conjugation homomorphism:

    1 → K* → GLₙ(K) → Aut_K(Mₙ(K)) → 1

  Combined with the Skolem-Noether theorem (surjectivity), this gives
  Aut_K(Mₙ(K)) ≅ GLₙ(K)/K* = PGLₙ(K).
-/

section PGLStructure

variable [Nonempty n]

/-- If conjAlgEquiv P = conjAlgEquiv Q, then QP⁻¹ commutes with all matrices. -/
theorem conjAlgEquiv_eq_implies_center (P Q : (Matrix n n K)ˣ)
    (h : conjAlgEquiv P = conjAlgEquiv Q) :
    ∀ A : Matrix n n K, (Q.val * P⁻¹.val) * A = A * (Q.val * P⁻¹.val) := by
  intro A
  have key : ∀ B : Matrix n n K, P⁻¹.val * B * P.val = Q⁻¹.val * B * Q.val := by
    intro B
    have := AlgEquiv.ext_iff.mp h B
    exact this
  -- From P⁻¹BP = Q⁻¹BQ for all B, multiply left by Q and right by P⁻¹
  -- Q(P⁻¹BP)P⁻¹ = Q(Q⁻¹BQ)P⁻¹
  -- (QP⁻¹)B(PP⁻¹) = (QQ⁻¹)B(QP⁻¹)
  -- (QP⁻¹)B = B(QP⁻¹)
  have step := key A
  -- step: P⁻¹AP = Q⁻¹AQ
  -- Multiply both sides on the left by Q and on the right by P⁻¹
  have lhs_calc : Q.val * (P⁻¹.val * A * P.val) * P⁻¹.val
      = (Q.val * P⁻¹.val) * A := by
    simp only [mul_assoc]
    rw [Units.mul_inv P, mul_one]
  have rhs_calc : Q.val * (Q⁻¹.val * A * Q.val) * P⁻¹.val
      = A * (Q.val * P⁻¹.val) := by
    simp only [mul_assoc]
    rw [← mul_assoc Q.val Q⁻¹.val, Units.mul_inv Q, one_mul]
  calc (Q.val * P⁻¹.val) * A
      = Q.val * (P⁻¹.val * A * P.val) * P⁻¹.val := lhs_calc.symm
    _ = Q.val * (Q⁻¹.val * A * Q.val) * P⁻¹.val := by rw [step]
    _ = A * (Q.val * P⁻¹.val) := rhs_calc

/-- Two units give the same conjugation automorphism if and only if their
    ratio QP⁻¹ is in the center of Mₙ(K) (i.e., is a scalar matrix). -/
theorem conjAlgEquiv_eq_iff_center (P Q : (Matrix n n K)ˣ) :
    conjAlgEquiv P = conjAlgEquiv Q ↔
    ∃ c : K, Q.val * P⁻¹.val = c • (1 : Matrix n n K) := by
  constructor
  · intro h
    exact (center_iff_scalar (Q.val * P⁻¹.val)).mp
      (conjAlgEquiv_eq_implies_center P Q h)
  · rintro ⟨c, hc⟩
    apply AlgEquiv.ext
    intro A
    -- Goal: conjAlgEquiv P A = conjAlgEquiv Q A (matrix equality)
    -- i.e., P⁻¹AP = Q⁻¹AQ
    -- From QP⁻¹ = cI, QP⁻¹ commutes with everything, so P⁻¹AP = Q⁻¹AQ
    have hcomm : (Q.val * P⁻¹.val) * A = A * (Q.val * P⁻¹.val) := by
      rw [hc]; exact scalar_commutes c A
    -- Suffices to show P⁻¹AP = Q⁻¹AQ
    -- Strategy: Q⁻¹AQ = Q⁻¹ · A · (QP⁻¹) · P (inserting P⁻¹P = 1)
    --         = Q⁻¹ · (QP⁻¹) · A · P (using commutativity)
    --         = (Q⁻¹Q) · P⁻¹ · A · P = P⁻¹AP
    suffices Q⁻¹.val * A * Q.val = P⁻¹.val * A * P.val by exact this.symm
    calc Q⁻¹.val * A * Q.val
        = Q⁻¹.val * A * (Q.val * P⁻¹.val * P.val) := by
          simp only [mul_assoc]; rw [Units.inv_mul P, mul_one]
      _ = Q⁻¹.val * (A * (Q.val * P⁻¹.val)) * P.val := by simp only [mul_assoc]
      _ = Q⁻¹.val * ((Q.val * P⁻¹.val) * A) * P.val := by rw [hcomm]
      _ = (Q⁻¹.val * Q.val) * (P⁻¹.val * A * P.val) := by simp only [mul_assoc]
      _ = P⁻¹.val * A * P.val := by rw [Units.inv_mul]; simp only [one_mul]

/-- The conjugation map is injective modulo the center: if conjAlgEquiv P
    sends every matrix to itself (i.e., P⁻¹AP = A for all A), then P is
    a scalar matrix. This is the kernel of the conjugation representation. -/
theorem conjAlgEquiv_eq_refl_iff (P : (Matrix n n K)ˣ) :
    conjAlgEquiv P = AlgEquiv.refl ↔
    ∃ c : K, P.val = c • (1 : Matrix n n K) := by
  constructor
  · intro h
    -- conjAlgEquiv P = id means P⁻¹AP = A for all A
    -- Multiply on left by P: P(P⁻¹AP) = PA, and LHS = AP
    -- Hence P is central, therefore scalar
    have hcomm : ∀ A : Matrix n n K, P.val * A = A * P.val := by
      intro A
      have key : P⁻¹.val * A * P.val = A := AlgEquiv.ext_iff.mp h A
      -- Left-multiply by P: P(P⁻¹AP) = PA
      have step := congr_arg (P.val * ·) key
      -- step: P * (P⁻¹AP) = P * A
      -- Simplify LHS: (PP⁻¹)(AP) = AP
      simp only [mul_assoc] at step
      rw [← mul_assoc P.val P⁻¹.val, Units.mul_inv, one_mul] at step
      -- step: A * P.val = P.val * A
      exact step.symm
    exact (center_iff_scalar P.val).mp hcomm
  · rintro ⟨c, hc⟩
    apply AlgEquiv.ext
    intro A
    -- Goal: conjAlgEquiv P A = AlgEquiv.refl A
    -- i.e., P⁻¹AP = A
    suffices P⁻¹.val * A * P.val = A by exact this
    -- P = cI commutes with A, so P⁻¹(AP) = P⁻¹(PA) = (P⁻¹P)A = A
    have hP_comm : P.val * A = A * P.val := by
      rw [hc]; exact scalar_commutes c A
    calc P⁻¹.val * A * P.val
        = P⁻¹.val * (A * P.val) := by rw [mul_assoc]
      _ = P⁻¹.val * (P.val * A) := by rw [hP_comm]
      _ = (P⁻¹.val * P.val) * A := by rw [mul_assoc]
      _ = 1 * A := by rw [Units.inv_mul]
      _ = A := one_mul A

end PGLStructure

end SkolemNoether
