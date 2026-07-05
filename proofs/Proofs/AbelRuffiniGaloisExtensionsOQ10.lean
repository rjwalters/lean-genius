/-
  Generic / regular realization of Sₙ and Aₙ as Galois groups
  (abel-ruffini-galois-extensions-oq-10 — the Sₙ/Aₙ case of the Regular Inverse
  Galois Problem).

  The symmetric group Sₙ = `Equiv.Perm (Fin n)` acts faithfully on the rational
  function field F = ℚ(x₁,…,xₙ) = `FractionRing (MvPolynomial (Fin n) ℚ)` by permuting
  the variables. Artin's fixed-field theorem (Mathlib `FixedPoints.toAlgAutMulEquiv`)
  then yields a group isomorphism

      Sₙ  ≃*  Gal(F / F^{Sₙ}),        with   [F : F^{Sₙ}] = n!,

  realizing Sₙ as a Galois group of a field extension, and likewise for the
  alternating subgroup Aₙ ≤ Sₙ. Both fixed fields are the symmetric-function fields
  ℚ(e₁,…,eₙ) resp. ℚ(e₁,…,eₙ)(√disc), which are purely transcendental over ℚ, so ℚ is
  algebraically closed in them and these are in fact *regular* realizations (the "R" in
  RIGP). We formalize the core Galois-group realization here.

  The abstract Artin engine is entirely in Mathlib; the only thing built here is the
  concrete permutation action on the fraction field. Rather than assemble it by hand,
  we route the already-bundled monoid hom `IsFractionRing.fieldEquivOfAlgEquivHom`
  through `MvPolynomial.renameEquiv`, which makes the two functoriality obligations
  (`map_one` / `map_mul`) fall out of `renameEquiv_refl` / `renameEquiv_trans`.

  Related gallery work: `AbelRuffiniGaloisExtensionsOQ01.lean` realizes the single group
  S₅ concretely (over ℚ, via `X⁵−4X+2`); the present file realizes *every* Sₙ and Aₙ
  simultaneously via the generic function-field construction.
-/
import Mathlib

open scoped Classical
open MvPolynomial

noncomputable section

variable (n : ℕ)

/-- The polynomial ring `ℚ[x₁,…,xₙ]`. -/
abbrev P : Type := MvPolynomial (Fin n) ℚ

/-- The rational function field `ℚ(x₁,…,xₙ)`. -/
abbrev F : Type := FractionRing (MvPolynomial (Fin n) ℚ)

/-! ### Step 1 — the permutation action on ℚ[x₁,…,xₙ] and its lift to ℚ(x₁,…,xₙ)

`MvPolynomial.renameEquiv ℚ e` permutes the variables. It is a monoid homomorphism from
`Sₙ` to the algebra automorphisms of `P` because both `Equiv.Perm` and the automorphism
group `P ≃ₐ[ℚ] P` multiply by reversed `trans`, so `renameEquiv_refl`/`renameEquiv_trans`
supply `map_one`/`map_mul`. -/

/-- `Sₙ = Perm (Fin n) →* (ℚ[x₁,…,xₙ] ≃ₐ[ℚ] ℚ[x₁,…,xₙ])` by permuting variables. -/
def renamePermHom : Equiv.Perm (Fin n) →* (P n ≃ₐ[ℚ] P n) where
  toFun e := MvPolynomial.renameEquiv ℚ e
  map_one' := MvPolynomial.renameEquiv_refl ℚ
  map_mul' e f := by
    show MvPolynomial.renameEquiv ℚ (e * f)
        = (MvPolynomial.renameEquiv ℚ f).trans (MvPolynomial.renameEquiv ℚ e)
    rw [MvPolynomial.renameEquiv_trans]
    -- `e * f = f.trans e` for permutations (both send `x ↦ e (f x)`).
    exact congrArg (MvPolynomial.renameEquiv ℚ) (Equiv.ext fun _ => rfl)

theorem renamePermHom_injective : Function.Injective (renamePermHom n) := by
  intro e₁ e₂ h
  apply Equiv.ext
  intro i
  have hx : (renamePermHom n e₁) (X i : P n) = (renamePermHom n e₂) (X i) :=
    AlgEquiv.congr_fun h (X i)
  have hX : (X (e₁ i) : P n) = X (e₂ i) := by
    simpa only [renamePermHom, MonoidHom.coe_mk, OneHom.coe_mk, renameEquiv_apply,
      rename_X] using hx
  exact MvPolynomial.X_injective hX

/-- The lift of the permutation action to the fraction field `F = ℚ(x₁,…,xₙ)`,
    obtained by composing `renamePermHom` with Mathlib's bundled
    `IsFractionRing.fieldEquivOfAlgEquivHom`. Since `ℚ` is a field it is its own fraction
    ring, so the target base field is `ℚ` itself. -/
def permToFAut : Equiv.Perm (Fin n) →* (F n ≃ₐ[ℚ] F n) :=
  (IsFractionRing.fieldEquivOfAlgEquivHom ℚ (F n)).comp (renamePermHom n)

theorem permToFAut_injective : Function.Injective (permToFAut n) := by
  simp only [permToFAut, MonoidHom.coe_comp]
  exact (IsFractionRing.fieldEquivOfAlgEquivHom_injective (A := ℚ) (B := P n)
    (K := ℚ) (L := F n)).comp (renamePermHom_injective n)

/-! ### Step 2 — the `Sₙ`-action on `F` and its faithfulness -/

/-- The permutation action of `Sₙ` on `F = ℚ(x₁,…,xₙ)`. -/
instance permAction : MulSemiringAction (Equiv.Perm (Fin n)) (F n) :=
  MulSemiringAction.compHom (F n) (permToFAut n)

instance permFaithful : FaithfulSMul (Equiv.Perm (Fin n)) (F n) where
  eq_of_smul_eq_smul {e₁ e₂} h := by
    apply permToFAut_injective n
    apply FaithfulSMul.eq_of_smul_eq_smul (α := F n)
    intro x
    exact h x

/-! ### Step 3 — Artin ⟹ `Sₙ` is a Galois group

Everything is a direct application of `Mathlib/FieldTheory/Fixed.lean`. -/

/-- **Sₙ realized as a Galois group.** `Equiv.Perm (Fin n) ≃* Gal(F / F^{Sₙ})`,
    where `F = ℚ(x₁,…,xₙ)` and `F^{Sₙ}` is the field of symmetric rational functions
    `ℚ(e₁,…,eₙ)`. -/
def realizeSn :
    Equiv.Perm (Fin n) ≃*
      (F n ≃ₐ[FixedPoints.subfield (Equiv.Perm (Fin n)) (F n)] F n) :=
  FixedPoints.toAlgAutMulEquiv _ _

/-- `F / F^{Sₙ}` is a (finite) Galois extension. -/
instance isGalois_Sn :
    IsGalois (FixedPoints.subfield (Equiv.Perm (Fin n)) (F n)) (F n) := inferInstance

/-- The generic `Sₙ` extension has degree `n!`. -/
theorem finrank_Sn :
    Module.finrank (FixedPoints.subfield (Equiv.Perm (Fin n)) (F n)) (F n)
      = Nat.factorial n := by
  rw [FixedPoints.finrank_eq_card]
  simp [Fintype.card_perm, Fintype.card_fin]

/-! ### Step 4 — `Aₙ` realized (same machinery, restricted to the alternating subgroup) -/

/-- The permutation action of `Aₙ ≤ Sₙ` on `F`, restricted along the subgroup inclusion. -/
instance altAction : MulSemiringAction (alternatingGroup (Fin n)) (F n) :=
  MulSemiringAction.compHom (F n)
    ((permToFAut n).comp (alternatingGroup (Fin n)).subtype)

theorem altToFAut_injective :
    Function.Injective ((permToFAut n).comp (alternatingGroup (Fin n)).subtype) := by
  simp only [MonoidHom.coe_comp]
  exact (permToFAut_injective n).comp (Subgroup.subtype_injective _)

instance altFaithful : FaithfulSMul (alternatingGroup (Fin n)) (F n) where
  eq_of_smul_eq_smul {e₁ e₂} h := by
    apply altToFAut_injective n
    apply FaithfulSMul.eq_of_smul_eq_smul (α := F n)
    intro x
    exact h x

/-- **Aₙ realized as a Galois group.** `alternatingGroup (Fin n) ≃* Gal(F / F^{Aₙ})`,
    with `F^{Aₙ} = ℚ(e₁,…,eₙ)(√disc)`. -/
def realizeAn :
    alternatingGroup (Fin n) ≃*
      (F n ≃ₐ[FixedPoints.subfield (alternatingGroup (Fin n)) (F n)] F n) :=
  FixedPoints.toAlgAutMulEquiv _ _

/-- `F / F^{Aₙ}` is a (finite) Galois extension. -/
instance isGalois_An :
    IsGalois (FixedPoints.subfield (alternatingGroup (Fin n)) (F n)) (F n) := inferInstance

/-- The generic `Aₙ` extension has degree `|Aₙ|` (which is `n!/2` for `n ≥ 2`). -/
theorem finrank_An :
    Module.finrank (FixedPoints.subfield (alternatingGroup (Fin n)) (F n)) (F n)
      = Fintype.card (alternatingGroup (Fin n)) := by
  rw [FixedPoints.finrank_eq_card]

end
