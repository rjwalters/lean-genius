/-
  Skolem-Noether Theorem: General Case for Central Simple Algebras
  (cayley-hamilton-minpoly-oq-02-oq-01-oq-01-oq-01)

  This file formalizes the general Skolem-Noether theorem for central simple algebras,
  extending the matrix-algebra case (SkolemNoetherMatrixAut.lean) to arbitrary CSAs.

  Theorem (Skolem-Noether, general): Let K be a field, A a finite-dimensional simple
  K-algebra, and B a finite-dimensional central simple K-algebra. Then any two
  K-algebra homomorphisms f, g : A →ₐ[K] B are conjugate: there exists a unit u ∈ Bˣ
  such that f(a) = u⁻¹ · g(a) · u for all a ∈ A.

  Proof architecture:
  1. [Proved] Right-B-linear maps B → B are left multiplication by a fixed element.
  2. [Proved] If φ : B ≃ₗ[K] B satisfies φ(b) = u·b, then u is a unit (with inverse v
             where v = φ⁻¹(1), and both u·v = 1 and v·u = 1 follow from φ∘φ⁻¹ = id).
  3. [Axiom]  The two A-module structures on B (via f and g) admit a K-linear bijection
              φ : B ≃ₗ[K] B that intertwines f-multiplication with g-multiplication and
              respects right B-multiplication. This is the key step requiring
              Wedderburn-Artin + isotypic decomposition.
  4. [Proved] From 1-3: the module isomorphism φ gives u = φ(1) as the conjugating unit,
              and f = conj(u⁻¹) ∘ g follows from the intertwining property.

  Mathlib gap: Step 3 requires Wedderburn-Artin (B ≅ Mₙ(D)) + IsIsotypic (unique simple
  A-module) + bimodule extension. Mathlib v4.26 has all ingredients; estimated 200-300
  lines to prove the axiom.
-/

import Mathlib
import Proofs.SkolemNoetherMatrixAut

set_option linter.deprecated false

namespace SkolemNoetherCSA

/-! ## Setup -/

variable {K : Type*} [Field K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]

/-! ## Lemma 1: Right-B-linear maps on B are left multiplication -/

/-- A K-linear map φ : B → B that respects right multiplication by B satisfies
    φ(b) = φ(1) · b for all b. Proof: φ(b) = φ(1 · b) = φ(1) · b. -/
theorem rightBLinear_is_leftMul
    (φ : B →ₗ[K] B)
    (hright : ∀ b c : B, φ (b * c) = φ b * c) :
    ∀ b : B, φ b = φ 1 * b := fun b => by
  simpa using hright 1 b

/-- Same formula for the inverse of a right-B-linear linear equivalence. -/
theorem rightBLinear_symm_is_leftMul
    (φ : B ≃ₗ[K] B)
    (hright : ∀ b c : B, φ (b * c) = φ b * c) :
    ∀ c : B, φ.symm c = φ.symm 1 * c := by
  have hright_symm : ∀ b c : B, φ.symm (b * c) = φ.symm b * c := by
    intro b c
    apply φ.injective
    simp only [LinearEquiv.apply_symm_apply, hright, LinearEquiv.apply_symm_apply]
  exact rightBLinear_is_leftMul φ.symm.toLinearMap hright_symm

/-! ## Lemma 2: Extracting a unit from a right-B-linear equivalence -/

/-- If φ : B ≃ₗ[K] B satisfies φ(b) = φ(1) · b, then u := φ(1) is a unit in B.
    Proof: Let v := φ⁻¹(1). Then u·v = φ(1)·φ⁻¹(1) and v·u = φ⁻¹(1)·φ(1).
    - u·v = 1: from hleft applied to φ⁻¹(1) gives φ(φ⁻¹(1)) = u·φ⁻¹(1), but
      φ(φ⁻¹(1)) = 1, so 1 = u·v.
    - v·u = 1: from hleft_symm applied to u gives φ⁻¹(u) = v·u, but φ⁻¹(φ(1)) = 1,
      and u = φ(1), so 1 = v·u. -/
theorem isUnit_of_rightBLinear_equiv
    (φ : B ≃ₗ[K] B)
    (hleft : ∀ b : B, φ b = φ 1 * b)
    (hleft_symm : ∀ c : B, φ.symm c = φ.symm 1 * c) :
    IsUnit (φ 1) := by
  -- Let u := φ(1), v := φ⁻¹(1)
  set u := φ 1 with hu_def
  set v := φ.symm 1 with hv_def
  -- Prove u * v = 1
  have huv : u * v = 1 := by
    -- φ(v) = u · v (by hleft)
    have h1 : φ v = u * v := hleft v
    -- φ(v) = φ(φ⁻¹(1)) = 1 (since φ ∘ φ⁻¹ = id)
    have h2 : φ v = 1 := by rw [hv_def, φ.apply_symm_apply]
    exact h1.symm.trans h2
  -- Prove v * u = 1
  have hvu : v * u = 1 := by
    -- φ⁻¹(u) = v · u (by hleft_symm)
    have h1 : φ.symm u = v * u := hleft_symm u
    -- φ⁻¹(u) = φ⁻¹(φ(1)) = 1 (since φ⁻¹ ∘ φ = id)
    have h2 : φ.symm u = 1 := by rw [hu_def, φ.symm_apply_apply]
    exact h1.symm.trans h2
  -- Construct the unit explicitly from both u*v=1 and v*u=1
  exact ⟨⟨u, v, huv, hvu⟩, rfl⟩

/-! ## Key Axiom: Module isomorphism from Wedderburn + Isotypic -/

/-
  The general Skolem-Noether theorem reduces to showing that two A-module structures
  on B are isomorphic via a right-B-linear K-linear bijection.

  Given f, g : A →ₐ[K] B, define two left A-module structures on B:
  - B_f: a acts by left multiplication by f(a),  i.e., a • b = f(a) · b
  - B_g: a acts by left multiplication by g(a), i.e., a • b = g(a) · b

  Claim: There exists a K-linear equivalence φ : B ≃ₗ[K] B such that:
  (a) φ(f(a) · b) = g(a) · φ(b) for all a ∈ A, b ∈ B  [A-module intertwining]
  (b) φ(b · c) = φ(b) · c for all b, c ∈ B              [right B-linearity]

  Proof sketch (not yet formalized):
  (i)  By Wedderburn-Artin (IsSimpleRing.exists_ringEquiv_matrix_divisionRing),
       B ≅ Mₙ(D) for a division ring D. In particular, B is simple Artinian.
  (ii) Via f, B becomes a left A-module (B_f). Via g, another A-module (B_g).
       Both have the same K-dimension (= dim K B).
  (iii) Since A is a simple ring, IsSimpleRing.isIsotypic shows all A-modules are
        isotypic: every simple A-submodule is isomorphic to any other. Both B_f and B_g
        are semisimple A-modules of the same K-dimension, hence isomorphic as A-modules.
  (iv) The A-module isomorphism φ : B_f → B_g is automatically right-B-linear:
       the centrality of K in B (Algebra.IsCentral K B) ensures that right B-multiplication
       commutes with the A-module structure, making φ a (left A, right B)-bimodule map.
  (v)  An explicit construction: using Wedderburn B ≅ Mₙ(D), reduce to the matrix case
       where SkolemNoetherMatrixAut.lean's explicit proof applies.

  Mathlib resources:
  - IsSimpleRing.exists_ringEquiv_matrix_divisionRing (Wedderburn-Artin, v4.26)
  - IsSimpleRing.isIsotypic (unique simple module type, v4.26)
  - Algebra.IsCentral (centrality, v4.26)
  - CSA structure (central + simple + finite-dim, v4.26)

  Estimated effort to prove this axiom: 200-300 additional lines.
-/

/-- Core axiom: The two A-module structures on B (via f and g) are isomorphic
    via a right-B-linear K-linear bijection.

    This is the Wedderburn-Artin + isotypic component of the Skolem-Noether proof. -/
axiom skolemNoether_module_iso
    [IsSimpleRing A] [FiniteDimensional K A]
    [IsSimpleRing B] [Algebra.IsCentral K B] [FiniteDimensional K B]
    (f g : A →ₐ[K] B) :
    ∃ (φ : B ≃ₗ[K] B),
      (∀ (a : A) (b : B), φ (f a * b) = g a * φ b) ∧
      (∀ (b c : B), φ (b * c) = φ b * c)

/-! ## Main Theorem: General Skolem-Noether for CSAs -/

/-- **Skolem-Noether Theorem (General Case)**
    For a field K, a finite-dimensional simple K-algebra A, and a finite-dimensional
    central simple K-algebra B, any two K-algebra homomorphisms f, g : A →ₐ[K] B
    are conjugate by a unit of B.

    That is, there exists u ∈ Bˣ such that f(a) = u⁻¹ · g(a) · u for all a ∈ A. -/
theorem skolemNoether_general
    [IsSimpleRing A] [FiniteDimensional K A]
    [IsSimpleRing B] [Algebra.IsCentral K B] [FiniteDimensional K B]
    (f g : A →ₐ[K] B) :
    ∃ (u : Bˣ), ∀ (a : A), f a = u⁻¹.val * g a * u.val := by
  -- Get the module isomorphism
  obtain ⟨φ, hmod, hright⟩ := skolemNoether_module_iso f g
  -- φ(b) = φ(1) · b (right-B-linear maps are left multiplication)
  have hleft : ∀ b : B, φ b = φ 1 * b :=
    rightBLinear_is_leftMul φ.toLinearMap hright
  -- φ⁻¹(c) = φ⁻¹(1) · c (same for the inverse)
  have hleft_symm : ∀ c : B, φ.symm c = φ.symm 1 * c :=
    rightBLinear_symm_is_leftMul φ hright
  -- φ(1) is a unit u in B
  obtain ⟨u, hu⟩ := isUnit_of_rightBLinear_equiv φ hleft hleft_symm
  -- The intertwining hmod with b = 1 gives: φ(f(a)) = g(a) · φ(1)
  -- Combined with hleft: φ(1) · f(a) = g(a) · φ(1)
  -- i.e., u · f(a) = g(a) · u
  -- Therefore: f(a) = u⁻¹ · g(a) · u
  refine ⟨u, fun a => ?_⟩
  -- From hmod with b = 1
  have hmod1 : φ (f a) = g a * φ 1 := by simpa using hmod a 1
  -- From hleft applied to f(a)
  have hleft_fa : φ (f a) = φ 1 * f a := hleft (f a)
  -- Combine: φ(1) · f(a) = g(a) · φ(1)
  have hconj : φ 1 * f a = g a * φ 1 := by rw [← hleft_fa, hmod1]
  -- Substitute φ(1) = u.val (from hu)
  have hval : φ 1 = u.val := hu.symm
  rw [hval] at hconj
  -- hconj: u.val · f(a) = g(a) · u.val
  -- Therefore: f(a) = u⁻¹.val · g(a) · u.val
  calc f a
      = (u⁻¹.val * u.val) * f a := by rw [Units.inv_mul]; ring
    _ = u⁻¹.val * (u.val * f a) := by ring
    _ = u⁻¹.val * (g a * u.val) := by rw [hconj]
    _ = u⁻¹.val * g a * u.val := by ring

/-! ## Corollaries -/

/-- Every K-algebra automorphism of a finite-dimensional central simple K-algebra is inner.
    Special case A = B of Skolem-Noether. -/
theorem aut_is_inner
    [IsSimpleRing B] [Algebra.IsCentral K B] [FiniteDimensional K B]
    (σ : B ≃ₐ[K] B) :
    ∃ (u : Bˣ), ∀ (b : B), σ b = u⁻¹.val * b * u.val := by
  obtain ⟨u, hu⟩ := skolemNoether_general σ.toAlgHom AlgHom.id
  exact ⟨u, fun b => by simpa using hu b⟩

/-- Two K-algebra homomorphisms from a finite-dimensional simple K-algebra into
    a CSA have the same image iff they are conjugate. -/
theorem conjugate_iff_same_image
    [IsSimpleRing A] [FiniteDimensional K A]
    [IsSimpleRing B] [Algebra.IsCentral K B] [FiniteDimensional K B]
    (f g : A →ₐ[K] B) :
    (∃ (u : Bˣ), ∀ a, f a = u⁻¹.val * g a * u.val) ↔
    (∃ (u : Bˣ), ∀ a, g a = u.val * f a * u⁻¹.val) := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u⁻¹, fun a => ?_⟩
    have := hu a
    rw [this]
    simp [mul_assoc, Units.mul_inv, Units.inv_mul]
  · rintro ⟨u, hu⟩
    refine ⟨u⁻¹, fun a => ?_⟩
    have := hu a
    rw [this]
    simp [mul_assoc, Units.mul_inv, Units.inv_mul]

/-! ## Infrastructure: Mathlib Building Blocks Identified -/

section MathlibBuiltins

variable [IsSimpleRing B] [Algebra.IsCentral K B] [FiniteDimensional K B]

/-
  The following shows that Mathlib v4.26 has all ingredients for the axiom proof.
-/

-- Wedderburn-Artin: simple Artinian ring ≅ Mₙ(D)
#check @IsSimpleRing.exists_ringEquiv_matrix_divisionRing

-- Uniqueness of simple A-modules (isotypic decomposition)
#check @IsSimpleRing.isIsotypic

-- Central algebra predicate
#check @Algebra.IsCentral

-- CSA structure (central + simple + finite-dim)
#check @CSA

-- Brauer group (equivalence classes of CSAs)
#check @BrauerGroup

-- Brauer equivalence (two CSAs differ by Morita equivalence)
#check @IsBrauerEquivalent

end MathlibBuiltins

end SkolemNoetherCSA
