/-
  Similarity invariance of the commutant dimension
  (cayley-hamilton-cyclic-vector-all-fields-oq-02-oq-02)

  The parent development pins the commutant dimension `dim_K C(M)` at the two
  ends of the Frobenius range `n ≤ dim_K C(M) ≤ n²`:

    * nonderogatory `M`      → `dim_K C(M) = n`   (main `OQ02OQ02` file);
    * scalar `M = c • I`     → `dim_K C(M) = n²`  (`…Scalar` file).

  A structural fact underlies *all* of Frobenius' theory: `dim_K C(M)` is a
  **similarity invariant** — it depends only on the conjugacy class of `M`.
  Conjugating `M ↦ U M U⁻¹` by an invertible matrix `U` is an algebra
  automorphism of `Mₙ(K)`, and an algebra automorphism carries the centralizer
  of `M` isomorphically onto the centralizer of its image.  Hence

      `dim_K C(U M U⁻¹) = dim_K C(M)`.

  This is exactly what makes the Frobenius formula
  `dim_K C(M) = Σ (2i-1) dᵢ` well-defined: the right-hand side is written in
  terms of the invariant factors, which are themselves similarity invariants,
  and the left-hand side must therefore be one too.

  We prove it in three reusable steps, valid for an arbitrary `K`-algebra `A`:

    1. `Subalgebra.map` of a centralizer under an `AlgEquiv` is the centralizer
       of the image set (`algEquiv_map_centralizer`);
    2. an `AlgEquiv` preserves the `K`-dimension of any subalgebra
       (`finrank_algEquiv_map`);
    3. conjugation by a unit is such an `AlgEquiv` (`ConjAct`), so the
       centralizer dimension is conjugation-invariant.

  Everything is `0`-sorry / `0`-axiom on top of Mathlib and the sibling files.
-/
import Mathlib
import Proofs.CayleyHamiltonCyclicVectorAllFieldsOQ02OQ02

open Matrix Polynomial

noncomputable section

namespace CyclicCommutantSimilarity

variable {K : Type*} [CommRing K]

/-! ### Step 1 — an `AlgEquiv` maps a centralizer to the centralizer of the image -/

/-- **Centralizers transport along algebra automorphisms.**  If `e : A ≃ₐ[K] A`
    is an algebra automorphism and `s ⊆ A`, then the image of the centralizer of
    `s` is the centralizer of the image `e '' s`:

      `e (C(s)) = C(e '' s)`.

    Concretely, `y` commutes with `e b` for every `b ∈ s` iff `e⁻¹ y` commutes
    with every `b ∈ s`; the automorphism turns each commutation relation into
    the corresponding one for the images. -/
theorem algEquiv_map_centralizer
    {A : Type*} [Semiring A] [Algebra K A] (e : A ≃ₐ[K] A) (s : Set A) :
    Subalgebra.map (e : A →ₐ[K] A) (Subalgebra.centralizer K s)
      = Subalgebra.centralizer K (e '' s) := by
  ext y
  simp only [Subalgebra.mem_map, Subalgebra.mem_centralizer_iff, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rintro g ⟨b, hb, rfl⟩
    rw [AlgHom.coe_coe, ← map_mul, ← map_mul, hx b hb]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro b hb
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy (e b) ⟨b, hb, rfl⟩

/-- Singleton form of `algEquiv_map_centralizer`: the centralizer of `{e M}` is
    the image under `e` of the centralizer of `{M}`. -/
theorem centralizer_singleton_algEquiv_apply
    {A : Type*} [Semiring A] [Algebra K A] (e : A ≃ₐ[K] A) (M : A) :
    Subalgebra.centralizer K ({e M} : Set A)
      = Subalgebra.map (e : A →ₐ[K] A) (Subalgebra.centralizer K {M}) := by
  rw [algEquiv_map_centralizer, Set.image_singleton]

/-! ### Step 2 — an `AlgEquiv` preserves subalgebra dimension -/

/-- **Algebra automorphisms preserve `K`-dimension.**  For any subalgebra
    `S ≤ A`, the image `S.map e` has the same `K`-dimension as `S`, because
    `AlgEquiv.subalgebraMap` is a `K`-linear isomorphism `S ≃ S.map e`. -/
theorem finrank_algEquiv_map
    {A : Type*} [Semiring A] [Algebra K A] (e : A ≃ₐ[K] A) (S : Subalgebra K A) :
    Module.finrank K ↥(Subalgebra.map (e : A →ₐ[K] A) S) = Module.finrank K ↥S :=
  ((e.subalgebraMap S).toLinearEquiv.finrank_eq).symm

/-! ### Step 3 — conjugation by a unit, and the invariance theorem -/

/-- **The commutant dimension is invariant under algebra automorphisms.**
    Applying any `e : A ≃ₐ[K] A` to `M` does not change the `K`-dimension of the
    centralizer:

      `dim_K C(e M) = dim_K C(M)`.

    Combine Step 1 (`e` carries `C(M)` onto `C(e M)`) with Step 2 (`e` preserves
    dimension). -/
theorem finrank_centralizer_algEquiv_apply
    {A : Type*} [Semiring A] [Algebra K A] (e : A ≃ₐ[K] A) (M : A) :
    Module.finrank K ↥(Subalgebra.centralizer K ({e M} : Set A))
      = Module.finrank K ↥(Subalgebra.centralizer K {M}) := by
  rw [centralizer_singleton_algEquiv_apply, finrank_algEquiv_map]

section Matrices

variable {n : ℕ}

/-- **Conjugation by a unit as an algebra automorphism.**  For an invertible
    matrix `U`, conjugation `X ↦ U X U⁻¹` is the algebra automorphism attached
    to `U` by the conjugation action `ConjAct`.  We package it as a named
    `AlgEquiv` so the invariance theorem reads cleanly. -/
def conjAlgEquiv (U : (Matrix (Fin n) (Fin n) K)ˣ) :
    Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K :=
  MulSemiringAction.toAlgEquiv K (Matrix (Fin n) (Fin n) K) (ConjAct.toConjAct U)

@[simp]
theorem conjAlgEquiv_apply (U : (Matrix (Fin n) (Fin n) K)ˣ)
    (X : Matrix (Fin n) (Fin n) K) :
    conjAlgEquiv U X = (↑U : Matrix (Fin n) (Fin n) K) * X * (↑U⁻¹ : Matrix (Fin n) (Fin n) K) := by
  simp only [conjAlgEquiv, MulSemiringAction.toAlgEquiv_apply,
    ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]

/-- **Commutant dimension is a conjugation invariant (unit form).**  For an
    invertible matrix `U` and any `M`,

      `dim_K C(U M U⁻¹) = dim_K C(M)`.

    This is `finrank_centralizer_algEquiv_apply` applied to the conjugation
    automorphism `conjAlgEquiv U`, with `conjAlgEquiv U M = U M U⁻¹`. -/
theorem finrank_centralizer_conj
    (U : (Matrix (Fin n) (Fin n) K)ˣ) (M : Matrix (Fin n) (Fin n) K) :
    Module.finrank K ↥(Subalgebra.centralizer K
        {(↑U : Matrix (Fin n) (Fin n) K) * M * (↑U⁻¹ : Matrix (Fin n) (Fin n) K)})
      = Module.finrank K ↥(Subalgebra.centralizer K {M}) := by
  have h := finrank_centralizer_algEquiv_apply (conjAlgEquiv U) M
  rwa [conjAlgEquiv_apply] at h

end Matrices

/-! ### Corollary over a field: nonderogatory is inherited by similar matrices -/

section Field

variable {F : Type*} [Field F] {n : ℕ}

/-- **A matrix similar to a nonderogatory matrix has commutant dimension `n`.**
    If `M` is nonderogatory (`minpoly = charpoly`) then `dim_F C(M) = n`
    (main file); by conjugation invariance, every conjugate `U M U⁻¹` also has
    `dim_F C = n`, even though we do not re-establish that the conjugate is
    itself nonderogatory. -/
theorem finrank_centralizer_conj_of_nonderogatory
    (U : (Matrix (Fin n) (Fin n) F)ˣ) (M : Matrix (Fin n) (Fin n) F)
    (hM : minpoly F M = M.charpoly) :
    Module.finrank F ↥(Subalgebra.centralizer F
        {(↑U : Matrix (Fin n) (Fin n) F) * M * (↑U⁻¹ : Matrix (Fin n) (Fin n) F)}) = n := by
  rw [finrank_centralizer_conj U M,
    CyclicCommutantDimension.finrank_centralizer_eq_of_nonderogatory M hM]

end Field

end CyclicCommutantSimilarity
