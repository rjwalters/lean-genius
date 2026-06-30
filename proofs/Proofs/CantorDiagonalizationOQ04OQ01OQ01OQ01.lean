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
closed category, a point-surjective `φ : A ⟶ (A ⟹ B)` forces every endomorphism
`t : B ⟶ B` to have a fixed global point.  This file cashes that abstract theorem
out in the two standard models.

### The bridge: categorical point-surjectivity is honest surjectivity in `Type`

The only real work is translating the categorical vocabulary into set-theoretic
language for `C = Type u`, where Mathlib supplies `CartesianClosed (Type u)`:

* the monoidal unit is `𝟙_ (Type u) = PUnit`, so a **global point** `𝟙_ ⟶ A` is
  literally a function `PUnit → A`, i.e. an element `a PUnit.unit : A`;
* the exponential is `A ⟹ B = (A → B)`, and **evaluation** `exp.ev` is honest
  function application `(a, h) ↦ h a` (`ev_apply`);
* hence `uncurry g (a, y) = g y a` (`uncurry_apply`), and the *name* of `f : A → B`
  evaluates to `f` itself: `name f PUnit.unit = f` (`name_apply`).

These collapse `LawvereCCC.PointSurjective φ` to `Function.Surjective φ`
(`pointSurjective_iff_surjective`).  Feeding a **fixed-point-free** endomorphism
through `lawvere_cantor` then yields the diagonal theorems.

### Results
* `ev_apply`, `uncurry_apply`, `name_apply` — the computational bridge in `Type`.
* `pointSurjective_iff_surjective` — `PointSurjective φ ↔ Function.Surjective φ`.
* `no_surjective_of_fixedPointFree` — for any `t : B → B` with no fixed point there
  is no surjection `A → (A → B)`.  This is Lawvere's diagonal in `Type`.
* `cantor_no_surjective` — **Cantor**: no surjection `A → (A → Bool)`, from the
  fixed-point-free `t = (!·)`.
* `lawvere_fixedPoint_presheaf`, `lawvere_cantor_presheaf` — the fixed-point form
  and its contrapositive in a presheaf topos `C ⥤ Type u`, using Mathlib's
  `CartesianClosed (C ⥤ Type u)` instance.

Everything is machine-checked with no `sorry` and no new axioms.
-/

universe u v

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.CartesianClosed
open LawvereCCC

namespace LawvereType

section TypeBridge

variable {A B X Y : Type u}

/-- **Evaluation in `Type` is honest application.**  The cartesian-closed
evaluation `exp.ev A` is, on the model `A ⟹ X = (A → X)`, the map
`(a, h) ↦ h a`. -/
lemma ev_apply (a : A) (h : A ⟹ X) : (exp.ev A).app X (a, h) = h a := rfl

/-- **Uncurrying in `Type` is honest application.**  For `g : Y ⟶ (A ⟹ X)`,
`uncurry g (a, y) = g y a`. -/
lemma uncurry_apply (g : Y ⟶ (A ⟹ X)) (a : A) (y : Y) :
    (CartesianClosed.uncurry g) (a, y) = g y a := by
  rw [CartesianClosed.uncurry_eq, types_comp_apply, whiskerLeft_apply, ev_apply]

/-- **The name of `f` evaluates to `f`.**  In `Type`, the categorical *name*
`name f : 𝟙_ ⟶ (A ⟹ B)` of a function `f : A → B` is the global point picking out
`f` itself: `name f PUnit.unit = f`. -/
lemma name_apply (f : A ⟶ B) : (name f) PUnit.unit = f := by
  funext a
  have h1 : CartesianClosed.uncurry (name f) = (ρ_ A).hom ≫ f := by
    rw [name_def, uncurry_curry]
  have h2 := congrFun h1 (a, PUnit.unit)
  rw [uncurry_apply] at h2
  rw [types_comp_apply, rightUnitor_hom_apply] at h2
  exact h2

/-- **Categorical point-surjectivity is honest surjectivity in `Type`.**  For a
function `φ : A → (A → B)`, viewed as a morphism `A ⟶ (A ⟹ B)`, the categorical
`PointSurjective φ` is equivalent to `Function.Surjective φ`. -/
theorem pointSurjective_iff_surjective (φ : A ⟶ (A ⟹ B)) :
    PointSurjective φ ↔ Function.Surjective φ := by
  constructor
  · intro hφ h
    obtain ⟨a, ha⟩ := hφ h
    refine ⟨a PUnit.unit, ?_⟩
    have := congrFun ha PUnit.unit
    rwa [types_comp_apply, name_apply] at this
  · intro hsurj f
    obtain ⟨a, ha⟩ := hsurj f
    refine ⟨fun _ => a, ?_⟩
    funext u
    have hu : u = PUnit.unit := rfl
    rw [types_comp_apply, hu, name_apply]
    exact ha

/-- **Lawvere's diagonal argument in `Type`.**  If `t : B → B` has no fixed point,
then there is no surjection `A → (A → B)`.  This is the decategorification of
`lawvere_cantor`: the diagonal `f a = t (φ a a)` would be a value `φ a` of a
surjection, but then `t` would fix `f a`. -/
theorem no_surjective_of_fixedPointFree {t : B → B} (ht : ∀ b, t b ≠ b)
    (φ : A → (A → B)) : ¬ Function.Surjective φ := by
  have hcat : ∀ s : 𝟙_ (Type u) ⟶ B, ¬ IsFixedPoint (t : B ⟶ B) s := by
    intro s hs
    have h := congrFun hs PUnit.unit
    rw [types_comp_apply] at h
    exact ht (s PUnit.unit) h
  intro hsurj
  exact lawvere_cantor hcat φ ((pointSurjective_iff_surjective φ).mpr hsurj)

end TypeBridge

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
  push_neg at h
  exact cantor_no_surjective A φ h

section Presheaf

variable {C : Type u} [SmallCategory C] {A B : C ⥤ Type u}

/-- **Lawvere's fixed-point theorem in a presheaf topos.**  Mathlib provides
`CartesianClosed (C ⥤ Type u)`, so the abstract theorem applies verbatim: a
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
