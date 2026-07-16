import Mathlib
import Proofs.CantorDiagonalizationOQ04OQ01OQ01

/-
# Instantiating Lawvere's Fixed-Point Theorem in `Type` and Presheaf Topoi

## Open Question (cantor-diagonalization-oq-04-oq-01-oq-01-oq-01)
"Instantiate this CCC theorem in concrete categories: derive Cantor's theorem in
`Type` (no surjection `A → (A → Bool)`) and the fixed-point form in a presheaf
topos as corollaries of `lawvere_fixedPoint`, by exhibiting the `CartesianClosed`
instances and a fixed-point-free `t`."

## Answer: YES.

The parent entry (`cantor-diagonalization-oq-04-oq-01-oq-01`) proves
`LawvereCCC.lawvere_fixedPoint` at full categorical generality: in *any* cartesian
closed category (Mathlib's `MonoidalClosed` over a `CartesianMonoidalCategory`), a
point-surjective `φ : A ⟶ (A ⟹ B)` forces every endomorphism `t : B ⟶ B` to have a
fixed global point.  This file cashes that abstract theorem out in the two standard
models.

### The bridge: categorical point-surjectivity is honest surjectivity in `Type`

The only real work is translating the categorical vocabulary into set-theoretic
language for `C = Type u`, where Mathlib supplies `MonoidalClosed (Type u)`:

* the monoidal unit is `𝟙_ (Type u) = PUnit`, so a **global point** `𝟙_ ⟶ A` is
  (the wrapper of) a function `PUnit → A`, i.e. an element `a PUnit.unit : A`;
* the internal hom is the hom-type itself: `A ⟹ B` is definitionally `A ⟶ B`
  (Mathlib's `TypeCat.Hom`, a structure wrapping `A → B`); the definitional
  bridges `elemToHom` / `homToElem` make this identification explicit;
* **evaluation** `ihom.ev` is honest function application `(a, h) ↦ h a`
  (`ev_apply`); hence `uncurry g (a, y) = g y a` (`uncurry_apply`), and the *name*
  of `f : A ⟶ B` evaluates to `f` itself: `name f PUnit.unit = f` (`name_apply`).

These collapse `LawvereCCC.PointSurjective φ` to `Function.Surjective` of the
underlying map (`pointSurjective_iff_surjective`).  Feeding a **fixed-point-free**
endomorphism through `lawvere_cantor` then yields the diagonal theorems.

### Results
* `ev_apply`, `uncurry_apply`, `name_apply` — the computational bridge in `Type`.
* `pointSurjective_iff_surjective` — `PointSurjective φ ↔ Function.Surjective` of
  the underlying map `a ↦ φ a`.
* `no_surjective_of_fixedPointFree` — for any `t : B → B` with no fixed point there
  is no surjection `A → (A → B)`.  This is Lawvere's diagonal in `Type`.
* `cantor_no_surjective` — **Cantor**: no surjection `A → (A → Bool)`, from the
  fixed-point-free `t = (!·)`.
* `lawvere_fixedPoint_presheaf`, `lawvere_cantor_presheaf` — the fixed-point form
  and its contrapositive in a presheaf topos `C ⥤ Type u`, using Mathlib's
  `MonoidalClosed (C ⥤ Type u)` instance.

Everything is machine-checked with no `sorry` and no new axioms.
-/

universe u v

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CategoryTheory.CartesianClosed
open LawvereCCC

namespace LawvereType

section TypeBridge

variable {A B X Y : Type u}

/-- **The internal hom of `Type` is the hom-type.**  An element of the exponential
object `A ⟹ X` *is*, definitionally, a morphism `A ⟶ X` (Mathlib's `TypeCat.Hom`
wrapper around `A → X`).  This definitional bridge makes the identification
explicit for the elaborator. -/
def elemToHom (h : A ⟹ X) : A ⟶ X := h

/-- The inverse definitional bridge: a morphism `A ⟶ X` as an element of the
exponential object `A ⟹ X`. -/
def homToElem (h : A ⟶ X) : A ⟹ X := h

@[simp] lemma elemToHom_homToElem (h : A ⟶ X) : elemToHom (homToElem h) = h := rfl

@[simp] lemma homToElem_elemToHom (h : A ⟹ X) : homToElem (elemToHom h) = h := rfl

lemma elemToHom_injective :
    Function.Injective (elemToHom : (A ⟹ X) → (A ⟶ X)) := fun _ _ h => h

/-- **Evaluation in `Type` is honest application.**  The cartesian-closed
evaluation `ihom.ev A` is, on the model `A ⟹ X ≃ (A → X)`, the map
`(a, h) ↦ h a`. -/
lemma ev_apply (a : A) (h : A ⟹ X) : (ihom.ev A).app X (a, h) = elemToHom h a := rfl

/-- **Uncurrying in `Type` is honest application.**  For `g : Y ⟶ (A ⟹ X)`,
`uncurry g (a, y) = g y a`. -/
lemma uncurry_apply (g : Y ⟶ (A ⟹ X)) (a : A) (y : Y) :
    (MonoidalClosed.uncurry g) (a, y) = elemToHom (g y) a := rfl

/-- **The name of `f` evaluates to `f`.**  In `Type`, the categorical *name*
`name f : 𝟙_ ⟶ (A ⟹ B)` of a morphism `f : A ⟶ B` is the global point picking out
`f` itself: `name f PUnit.unit = f`. -/
lemma name_apply (f : A ⟶ B) : elemToHom ((name f) PUnit.unit) = f := by
  have h1 : MonoidalClosed.uncurry (name f) = (ρ_ A).hom ≫ f := by
    rw [name_def, uncurry_curry]
  ext a
  have h2 := types_congr_hom h1 (a, PUnit.unit)
  rw [uncurry_apply] at h2
  rw [types_comp_apply, rightUnitor_hom_apply] at h2
  exact h2

/-- **Categorical point-surjectivity is honest surjectivity in `Type`.**  For a
morphism `φ : A ⟶ (A ⟹ B)`, the categorical `PointSurjective φ` is equivalent to
`Function.Surjective` of the underlying map `a ↦ φ a : A → (A ⟶ B)`. -/
theorem pointSurjective_iff_surjective (φ : A ⟶ (A ⟹ B)) :
    PointSurjective φ ↔ Function.Surjective (fun a => elemToHom (φ a)) := by
  constructor
  · intro hφ h
    obtain ⟨a, ha⟩ := hφ h
    refine ⟨a PUnit.unit, ?_⟩
    have hpt := types_congr_hom ha PUnit.unit
    rw [types_comp_apply] at hpt
    show elemToHom (φ (a PUnit.unit)) = h
    rw [hpt]
    exact name_apply h
  · intro hsurj f
    obtain ⟨a, ha⟩ := hsurj f
    refine ⟨TypeCat.ofHom fun _ => a, ?_⟩
    have key : φ a = name f PUnit.unit :=
      elemToHom_injective (ha.trans (name_apply f).symm)
    ext u
    show φ ((TypeCat.ofHom fun _ => a) u) = (name f) u
    have hu : u = PUnit.unit := rfl
    rw [hu]
    exact key

end TypeBridge

/-- **Lawvere's diagonal argument in `Type`.**  If `t : B → B` has no fixed point,
then there is no surjection `A → (A → B)`.  This is the decategorification of
`lawvere_cantor`: the diagonal `f a = t (φ a a)` would be a value `φ a` of a
surjection, but then `t` would fix `f a`. -/
theorem no_surjective_of_fixedPointFree {A B : Type u} {t : B → B} (ht : ∀ b, t b ≠ b)
    (φ : A → (A → B)) : ¬ Function.Surjective φ := by
  intro hsurj
  -- package the data categorically
  set Φ : A ⟶ (A ⟹ B) := TypeCat.ofHom fun a => homToElem (TypeCat.ofHom (φ a)) with hΦ
  have hcat : ∀ s : 𝟙_ (Type u) ⟶ B, ¬ IsFixedPoint (TypeCat.ofHom t) s := by
    intro s hs
    have h := types_congr_hom hs PUnit.unit
    rw [types_comp_apply, TypeCat.ofHom_apply] at h
    exact ht (s PUnit.unit) h
  have hΦsurj : Function.Surjective (fun a => elemToHom (Φ a)) := by
    intro g
    obtain ⟨a, ha⟩ := hsurj (g : A → B)
    refine ⟨a, ?_⟩
    show elemToHom (Φ a) = g
    rw [hΦ, TypeCat.ofHom_apply, elemToHom_homToElem, ha, TypeCat.ofHom_eq]
  exact lawvere_cantor hcat Φ ((pointSurjective_iff_surjective Φ).mpr hΦsurj)

/-- **Cantor's theorem, as a corollary of Lawvere.**  There is no surjection
`A → (A → Bool)`, because `t = (!·)` is a fixed-point-free endomorphism of `Bool`.
This recovers the classical diagonal `Function.cantor_surjective` purely from the
categorical fixed-point theorem. -/
theorem cantor_no_surjective (A : Type) (φ : A → (A → Bool)) :
    ¬ Function.Surjective φ :=
  no_surjective_of_fixedPointFree (t := fun b => !b) Bool.not_ne_self φ

/-- **Existence of a missed map.**  Restating Cantor: for every `φ : A → (A → Bool)`
some `g : A → Bool` lies outside its image — the diagonal complement. -/
theorem cantor_exists_missed (A : Type) (φ : A → (A → Bool)) :
    ∃ g : A → Bool, ∀ a, φ a ≠ g := by
  by_contra h
  push Not at h
  exact cantor_no_surjective A φ h

section Presheaf

variable {C : Type u} [SmallCategory C] {A B : C ⥤ Type u}

/-- **Lawvere's fixed-point theorem in a presheaf topos.**  Mathlib provides
`MonoidalClosed (C ⥤ Type u)`, so the abstract theorem applies verbatim: a
point-surjective `φ : A ⟶ (A ⟹ B)` of presheaves forces every endomorphism
`t : B ⟶ B` to have a fixed global point. -/
theorem lawvere_fixedPoint_presheaf {φ : A ⟶ (A ⟹ B)} (hφ : PointSurjective φ)
    (t : B ⟶ B) : ∃ s : 𝟙_ (C ⥤ Type u) ⟶ B, IsFixedPoint t s :=
  lawvere_fixedPoint hφ t

/-- **The Cantor obstruction in a presheaf topos.**  If a presheaf endomorphism
`t : B ⟶ B` is fixed-point free, no `φ : A ⟶ (A ⟹ B)` can be point-surjective. -/
theorem lawvere_cantor_presheaf {t : B ⟶ B}
    (ht : ∀ s : 𝟙_ (C ⥤ Type u) ⟶ B, ¬ IsFixedPoint t s)
    (φ : A ⟶ (A ⟹ B)) : ¬ PointSurjective φ :=
  lawvere_cantor ht φ

end Presheaf

end LawvereType
