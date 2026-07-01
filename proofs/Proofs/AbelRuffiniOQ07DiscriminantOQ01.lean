/-
  The Discriminant–Square Criterion:
    Gal(f) ⊆ Aₙ  ⟺  disc(f) is a square in the base field
  (Open Question OQ-01 of `abel-ruffini-oq-07-discriminant`)

  ## Background
  The parent entry `AbelRuffiniOQ07Discriminant.lean` reduces
  `Gal(X⁵ − X − 1 / ℚ) ≅ S₅` to a discriminant assembler
  (`gal_eq_top_of_transitive_threeCycle_odd`) that takes, as a *hypothesis*, the
  existence of an odd permutation in the Galois group.  It supplies the arithmetic
  fact `disc = 2869` is not a perfect square (`disc_not_square`) but leaves the
  bridge

      disc(f) is not a square in the base field  ⟹  Gal(f) contains an odd permutation

  as an assumption, because Mathlib v4.26.0 has neither the polynomial discriminant
  `∏_{i<j}(rⱼ − rᵢ)²` nor the classical criterion connecting it to the alternating
  group.  This file formalizes that bridge in full generality.

  ## The mathematical content
  Let `E/F` be a finite Galois extension and `r : Fin n → E` a family of *distinct*
  elements which the Galois group permutes (the roots of a separable polynomial).
  Set

      δ  :=  ∏_{i<j} (rⱼ − rᵢ)      (the Vandermonde difference product)
      disc :=  δ²                    (the discriminant).

  The two classical facts are:

    * **Sign transformation.**  Any `φ ∈ Gal(E/F)` permutes the `rᵢ` by some
      `σ ∈ Sₙ`, and then `φ(δ) = sign(σ) · δ`.  (Antisymmetry of the Vandermonde
      determinant.)  Hence `φ` fixes `δ` iff `σ` is even.

    * **Galois descent.**  `δ` lies in the base field `F` iff every `φ ∈ Gal(E/F)`
      fixes it (`IsGalois.mem_range_algebraMap_iff_fixed`).

  Combining, and using `disc = δ²` together with `δ ≠ 0` and `2 ≠ 0`:

      disc is a square in F  ⟺  δ ∈ F  ⟺  every σ is even  ⟺  Gal(f) ⊆ Aₙ.

  ## What this file verifies (0 sorry, 0 axiom)
    * `diffProd` — the difference product `∏_{i<j}(rⱼ − rᵢ)`, as a Vandermonde
      determinant, with `diffProd_eq_prod` giving the classical product form.
    * `diffProd_comp_perm` — the **sign transformation**
      `diffProd (r ∘ σ) = sign σ • diffProd r` (fills the Mathlib gap).
    * `algEquiv_diffProd` — a Galois automorphism sends `δ` to the permuted `δ`.
    * `algEquiv_fixes_diffProd_iff_sign_one` — `φ` fixes `δ` iff its permutation is even.
    * `disc_isSquare_iff_gal_le_alternating` — **the criterion**:
        disc is a square in F  ⟺  Gal(f) ⊆ Aₙ.
    * `exists_odd_of_disc_not_square` — the exact form the parent needs:
        disc not a square ⟹ some `φ` acts by an odd permutation.

  Everything is fully machine-checked with 0 sorries and 0 axioms.
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

open Matrix Equiv Equiv.Perm

namespace AbelRuffiniDiscriminantSquare

/-!
## The difference product (square root of the discriminant)

Over any commutative ring, the difference product `∏_{i<j}(rⱼ − rᵢ)` is the
determinant of the Vandermonde matrix of the family.  We take this as the
definition of `δ` and recover the product form from `Matrix.det_vandermonde`.
-/

variable {R : Type*} [CommRing R]

/-- The **difference product** `δ = ∏_{i<j}(rⱼ − rᵢ)` of a finite family, realized
as the Vandermonde determinant.  Its square is the discriminant. -/
noncomputable def diffProd {n : ℕ} (r : Fin n → R) : R := (Matrix.vandermonde r).det

/-- `δ` equals the classical difference product `∏_{i<j}(rⱼ − rᵢ)`. -/
theorem diffProd_eq_prod {n : ℕ} (r : Fin n → R) :
    diffProd r = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (r j - r i) :=
  Matrix.det_vandermonde r

/-- Precomposing the family with a permutation `σ` is the same as permuting the rows
of the Vandermonde matrix. -/
theorem vandermonde_comp_perm {n : ℕ} (r : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    Matrix.vandermonde (r ∘ σ) = (Matrix.vandermonde r).submatrix σ id := by
  ext i j
  simp [Matrix.vandermonde_apply, Matrix.submatrix_apply]

/-- **Sign transformation of the difference product.**  Permuting the family by `σ`
multiplies the difference product by `sign σ`.  This is the antisymmetry of the
Vandermonde determinant; it is the algebraic heart of the discriminant criterion. -/
theorem diffProd_comp_perm {n : ℕ} (r : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    diffProd (r ∘ σ) = (Equiv.Perm.sign σ : ℤ) • diffProd r := by
  unfold diffProd
  rw [vandermonde_comp_perm, Matrix.det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp

/-!
## Galois action on the difference product

From now on we work with a Galois automorphism of a field extension `E/F` that
permutes a distinguished family `r : Fin n → E`.
-/

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- A Galois automorphism `φ` which permutes `r` by `σ` sends `δ = diffProd r` to the
difference product of the permuted family. -/
theorem algEquiv_diffProd {n : ℕ} (r : Fin n → E) (f : E ≃ₐ[F] E)
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ i, f (r i) = r (σ i)) :
    f (diffProd r) = diffProd (r ∘ σ) := by
  unfold diffProd
  rw [AlgEquiv.map_det]
  congr 1
  ext i j
  simp only [AlgEquiv.mapMatrix_apply, Matrix.map_apply, Matrix.vandermonde_apply,
    Function.comp_apply]
  rw [map_pow, hσ]

/-- **`φ` fixes `δ` iff its permutation is even.**  For distinct `r` in a field with
`2 ≠ 0`, a Galois automorphism `φ` fixes the difference product exactly when the
permutation `σ` it induces on `r` is even. -/
theorem algEquiv_fixes_diffProd_iff_sign_one {n : ℕ} (r : Fin n → E)
    (hr : Function.Injective r) (h2 : (2 : E) ≠ 0) (f : E ≃ₐ[F] E)
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ i, f (r i) = r (σ i)) :
    f (diffProd r) = diffProd r ↔ Equiv.Perm.sign σ = 1 := by
  have hne : diffProd r ≠ 0 := by
    rw [diffProd]; exact Matrix.det_vandermonde_ne_zero_iff.mpr hr
  rw [algEquiv_diffProd r f hσ, diffProd_comp_perm, zsmul_eq_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · simp
  · simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
    constructor
    · intro he
      have h2δ : (2 : E) * diffProd r = 0 := by linear_combination -he
      rcases mul_eq_zero.mp h2δ with hh | hh
      · exact absurd hh h2
      · exact absurd hh hne
    · intro he; exact absurd he (by decide)

/-!
## The criterion
-/

variable {n : ℕ} (r : Fin n → E) [FiniteDimensional F E] [IsGalois F E]

/-- The difference product lies in the base field iff it is fixed by the whole
Galois group.  A direct instance of the Galois descent lemma. -/
theorem diffProd_mem_range_iff_fixed :
    diffProd r ∈ Set.range (algebraMap F E) ↔ ∀ f : E ≃ₐ[F] E, f (diffProd r) = diffProd r :=
  IsGalois.mem_range_algebraMap_iff_fixed (diffProd r)

/-- **The Discriminant–Square Criterion.**  Let `E/F` be a finite Galois extension,
`r : Fin n → E` a family of distinct elements permuted by the Galois group, in a
field where `2 ≠ 0`.  Then the discriminant `disc = δ²` is a square in the base
field `F` if and only if every element of the Galois group acts on `r` by an even
permutation (i.e. `Gal ⊆ Aₙ`). -/
theorem disc_isSquare_iff_gal_le_alternating
    (hr : Function.Injective r) (h2 : (2 : E) ≠ 0)
    (hperm : ∀ f : E ≃ₐ[F] E, ∃ σ : Equiv.Perm (Fin n), ∀ i, f (r i) = r (σ i)) :
    (∃ c : E, c ∈ Set.range (algebraMap F E) ∧ c ^ 2 = diffProd r ^ 2)
      ↔ (∀ (f : E ≃ₐ[F] E) (σ : Equiv.Perm (Fin n)),
            (∀ i, f (r i) = r (σ i)) → Equiv.Perm.sign σ = 1) := by
  -- Step 1: `disc` is a square in `F`  ⟺  `δ ∈ F`.
  have step1 :
      (∃ c : E, c ∈ Set.range (algebraMap F E) ∧ c ^ 2 = diffProd r ^ 2)
        ↔ diffProd r ∈ Set.range (algebraMap F E) := by
    constructor
    · rintro ⟨c, ⟨a, ha⟩, hc2⟩
      -- `c² = δ²` ⟹ `(c − δ)(c + δ) = 0` ⟹ `δ = c` or `δ = −c`; both lie in `F`.
      have h0 : (c - diffProd r) * (c + diffProd r) = 0 := by linear_combination hc2
      rcases mul_eq_zero.mp h0 with h | h
      · exact ⟨a, by rw [ha]; linear_combination h⟩
      · exact ⟨-a, by rw [map_neg, ha]; linear_combination -h⟩
    · rintro hδ
      exact ⟨diffProd r, hδ, rfl⟩
  -- Step 2: `δ ∈ F`  ⟺  every automorphism fixes `δ`.
  rw [step1, diffProd_mem_range_iff_fixed]
  -- Step 3: every automorphism fixes `δ`  ⟺  every induced permutation is even.
  constructor
  · intro hfix f σ hσ
    exact (algEquiv_fixes_diffProd_iff_sign_one r hr h2 f hσ).mp (hfix f)
  · intro heven f
    obtain ⟨σ, hσ⟩ := hperm f
    exact (algEquiv_fixes_diffProd_iff_sign_one r hr h2 f hσ).mpr (heven f σ hσ)

/-- **The form the parent entry needs.**  If the discriminant `δ²` is *not* a square
in the base field `F`, then some element of the Galois group acts on the roots by an
*odd* permutation.  This discharges the odd-permutation hypothesis of the parent's
assembler `gal_eq_top_of_transitive_threeCycle_odd` directly from a non-square
discriminant. -/
theorem exists_odd_of_disc_not_square
    (hr : Function.Injective r) (h2 : (2 : E) ≠ 0)
    (hperm : ∀ f : E ≃ₐ[F] E, ∃ σ : Equiv.Perm (Fin n), ∀ i, f (r i) = r (σ i))
    (hns : ¬ ∃ c : E, c ∈ Set.range (algebraMap F E) ∧ c ^ 2 = diffProd r ^ 2) :
    ∃ (f : E ≃ₐ[F] E) (σ : Equiv.Perm (Fin n)),
      (∀ i, f (r i) = r (σ i)) ∧ σ ∉ alternatingGroup (Fin n) := by
  by_contra hcon
  push_neg at hcon
  refine hns ((disc_isSquare_iff_gal_le_alternating r hr h2 hperm).mpr ?_)
  intro f σ hσ
  rw [← Equiv.Perm.mem_alternatingGroup]
  exact hcon f σ hσ

end AbelRuffiniDiscriminantSquare
